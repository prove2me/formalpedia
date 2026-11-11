-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_37
-- name    : WeakStrongMSR.lemma_3_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:32:12.241418+00:00
-- url     : https://prove2.me/theorems/53a97ff1-779c-4824-841f-315e62a884a6
-- title:
--   Lemma 3.37 — binary search: at most $2+\lceil\log_2|\mathrm{TEST}|\rceil$ tests; whp a valid solution of cost $\le 3000\,\mathrm{OPT}$
-- statement:
--   Run Algorithm 5 with absolute constant $c$, $h$ of Eq. (20), an LP routine selecting optimal solutions, $\varepsilon\in(0,1]$ and an offline routine with guarantee $3+\varepsilon$. Let $\mathrm{TEST}$ be the grid of guesses and $C=3000$.
--
--   There is an absolute $c_0$ such that for every $c\ge c_0$ there is $a>0$, and for every exponent $e$ there is $n_0$, with the following properties, for every $\delta\in(0,\tfrac12)$, $n\ge n_0$, $k\ge1$, metric $d$, bound $\mathrm{aspect}(d)\le\Delta$ and adversary.
--   1. On every weak-distance table and every outcome, Algorithm 5 runs at most $2+\lceil\log_2|\mathrm{TEST}|\rceil$ tests.
--   2. If $\Delta\ge1$, then $|\mathrm{TEST}|\le 2+\log_2(2C\Delta^2)$. So for $\Delta\le n^e$ the number of tests is $O(\log\log n)$.
--   3. If $\Delta\le n^e$, then with probability at least $1-n^{-a}$ the output is a valid solution of total radius at most $C\cdot\mathrm{OPT}$.
--
--   Differences from the source:
--   - generalization: main text δ = 1/3, h = 32⌈c log n/32⌉ (and threshold 2c(·)) → every δ ∈ (0, 1/2), h = 32⌈c log n/(32γ²)⌉ (Eq. (20)) and threshold (2c/γ)(·) (Eq. (21)); reason: App. A, pp.34–36, runs the same algorithm with these parameters for Theorem A.1; at δ = 1/3 it is the main-text algorithm with c renamed (h = 32⌈36c log n/32⌉)
--   - generalization: "solve (1)", "the (3+ϵ)-approximation of [BERW24]" → every LP routine selecting optimal solutions and every offline routine covering S with cost ≤ (3+ε)·opt_S; reason: the statement holds for every such routine, in particular for the paper's
--   - encoding: the algorithm of §3 described in prose (free choices "any one", "consistently", "a middle value") → the definitions WeakStrongMSR.Sampling/Rounding/Repair/Compress/Test, with ties fixed (insertion order, first conflicting candidate, least-index root, least-index list, ⌊(i+j)/2⌋, u, v = points 0, 1); reason: the paper leaves these choices free; each fixed choice is one admissible run of the paper's algorithm
--   - reading: "with high probability" → ∃ c₀ ∀ c ≥ c₀ ∃ a > 0 ∀ e ∃ n₀: probability ≥ 1 − n^{−a} when Δ ≤ n^e, n ≥ n₀; reason: the union bound runs over the O(e log n) grid values (§2.3: Δ ≤ n^{O(1)})
--   - reading: O(log log n) tests on every run; cost O(OPT) → at most 2 + ⌈log₂|TEST|⌉ tests with |TEST| ≤ 2 + log₂(2CΔ²); cost ≤ C·OPT with C = 3000; reason: the counts of Algorithm 5 and the bound Ckλ_ub < C·OPT of the proof (cost 0 = OPT when k ≥ n)
--   - generalization: resource bounds for the runs of the model (weak table d̃ = weakDist d C adv) → the bound holds on every run for every table w : Fin n → Fin n → ℝ; reason: the worst-case count never depends on the honesty of w; it specializes to w = weakDist d C adv
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.37, p.28 (PDF 29); Algorithm 5, p.28; §3.5, p.27

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates
import Definitions.Def_WeakStrongMSR_Draws
import Definitions.Def_WeakStrongMSR_LP
import Definitions.Def_WeakStrongMSR_Sampling
import Definitions.Def_WeakStrongMSR_Rounding
import Definitions.Def_WeakStrongMSR_Repair
import Definitions.Def_WeakStrongMSR_Compress
import Definitions.Def_WeakStrongMSR_Test

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.37** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.28, PDF p.29; Algorithm 5, p.28; the grid of §3.5, p.27).
"Binary search makes O(log log n) tests on every run. With high probability, it returns a valid
solution of cost O(OPT)."

There is an absolute `c₀` such that for every `c ≥ c₀` there is `a > 0`, and for every aspect-ratio
exponent `e` there is `n₀`, with: for every `δ ∈ (0, 1/2)`, `n ≥ n₀`, `k ≥ 1`, metric `d`,
aspect-ratio bound `Δ` with `aspect(d) ≤ Δ`, adversary, LP routine returning optimal solutions,
`ε ∈ (0, 1]` and offline routine with guarantee `(3 + ε)`:
1. on every weak table and every outcome, Algorithm 5 runs at most `2 + ⌈log₂ |TEST|⌉` tests;
2. if `Δ ≥ 1`, the grid has `|TEST| ≤ 2 + log₂(2C∆²)` values (`C = 3000`), so for `Δ ≤ n^e` the
   number of tests is `O(log log n)`;
3. if `Δ ≤ n^e`, with probability at least `1 − n^{−a}` the output is a valid solution of total
   radius at most `C · OPT = 3000 · OPT`.

**Formalization Note.** The search is `WeakStrongMSR.guessLaw` (independent tests at every grid
value, R13). `O(OPT)` is the explicit `C · OPT` of the proof; for `k ≥ n` the output costs `0`. -/
theorem lemma_3_37 :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ a : ℝ, 0 < a ∧ ∀ e : ℕ, ∃ n₀ : ℕ,
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k →
    ∀ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d → ∀ Δ : ℝ, aspectRatio d ≤ Δ →
    ∀ adv : Adversary n, ∀ sel : LPSelector n, SelectsOptimal sel →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ off : OfflineRoutine n k, GoodOffline d ε off →
      (∀ (w : Fin n → Fin n → ℝ), ∀ g ∈ (guessLaw c δ k Δ sel off d w).support,
        g.tests ≤ 2 + Nat.clog 2 (testGrid d k Δ).length) ∧
      (1 ≤ Δ → ((testGrid d k Δ).length : ℝ) ≤ 2 + Real.logb 2 (2 * 3000 * Δ ^ 2)) ∧
      (Δ ≤ (n : ℝ) ^ e →
        ENNReal.ofReal (1 - (n : ℝ) ^ (-a)) ≤
          jointProb δ (fun C => guessLaw c δ k Δ sel off d (weakDist d C adv))
            (fun _ g => ∃ s, g.sol = some s ∧ ValidSolution d s.σ s.ctr s.rad ∧
              solCost s.rad ≤ 3000 * MinSumRadiiPTAS.Main.msrOpt d k)) := by sorry

end WeakStrongMSR
