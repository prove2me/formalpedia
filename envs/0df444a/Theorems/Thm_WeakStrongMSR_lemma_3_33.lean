-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_33
-- name    : WeakStrongMSR.lemma_3_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:31:32.955298+00:00
-- url     : https://prove2.me/theorems/06d31350-4f1f-4730-af44-e9d3774c9779
-- title:
--   Lemma 3.33 — one test: whp a completed run is valid; for $\lambda\ge\mathrm{OPT}/(2k)$, whp no abort and radius $<2158k\lambda$
-- statement:
--   Run one test (sampling, rounding, repair, compression) of a guess $\lambda>0$. Use the absolute constant $c$, $h$ of Eq. (20), an LP routine that selects optimal solutions, $0<\varepsilon\le1$, and an offline routine covering every $S$ with cost at most $(3+\varepsilon)\,\mathrm{opt}_S$.
--
--   There is an absolute $c_0$ such that for every $c\ge c_0$ there are $a>0$ and $n_0$ with the following properties, for every $\delta\in(0,\tfrac12)$, $n\ge n_0$, $k\ge1$, metric $d$ and adversary.
--   1. With probability at least $1-n^{-a}$, the test aborts or returns a valid solution: at most $k$ balls, with every point in the ball of its slot.
--   2. If $\lambda\ge\mathrm{OPT}/(2k)$, then with probability at least $1-n^{-a}$ the test does not abort and returns a valid solution of total radius less than $2158k\lambda$.
--   3. Consider any weak-distance table and any run that completes repair. If $\lambda\ge\mathrm{OPT}/(2k)$ and the selected family has total radius below $51k\lambda$ (the guarantee of Lemma 3.17), then the compressed solution has total radius
--   $$<4(3+\varepsilon)k\lambda+42\cdot 51k\lambda\le 2158k\lambda .$$
--
--   Hence it is at most $Ck\lambda$ for $C=3000$.
--
--   Differences from the source:
--   - generalization: main text δ = 1/3, h = 32⌈c log n/32⌉ (and threshold 2c(·)) → every δ ∈ (0, 1/2), h = 32⌈c log n/(32γ²)⌉ (Eq. (20)) and threshold (2c/γ)(·) (Eq. (21)); reason: App. A, pp.34–36, runs the same algorithm with these parameters for Theorem A.1; at δ = 1/3 it is the main-text algorithm with c renamed (h = 32⌈36c log n/32⌉)
--   - reading: "with high probability", "a sufficiently large constant c" → ∃ c₀, ∀ c ≥ c₀, ∃ a > 0, ∃ n₀: probability ≥ 1 − n^{−a} for n ≥ n₀, with c₀, a, n₀ independent of δ; reason: §2.3: whp = 1 − n^{−Ω(1)}; App. A: every bound fails with probability n^{−Ω(c)} for an absolute c
--   - generalization: "solve (1)", "the (3+ϵ)-approximation of [BERW24]" → every LP routine selecting optimal solutions and every offline routine covering S with cost ≤ (3+ε)·opt_S; reason: the statement holds for every such routine, in particular for the paper's
--   - encoding: the algorithm of §3 described in prose (free choices "any one", "consistently", "a middle value") → the definitions WeakStrongMSR.Sampling/Rounding/Repair/Compress/Test, with ties fixed (insertion order, first conflicting candidate, least-index root, least-index list, ⌊(i+j)/2⌋, u, v = points 0, 1); reason: the paper leaves these choices free; each fixed choice is one admissible run of the paper's algorithm
--   - reading: "its total radius is O(kλ)" → total radius < 2158kλ; reason: the "more precisely" sentence of the lemma
--   - generalization: "if λ ≥ OPT/(2k) and the guarantees of Lemmas 3.17 and 3.21 hold" → clause 3 assumes λ ≥ OPT/(2k) and ∑ R_i < 51kλ only, on every run that completes repair; reason: the cost bound uses only these; the guarantees of Lemma 3.21 give validity, not cost
--   - generalization: resource bounds for the runs of the model (weak table d̃ = weakDist d C adv) → the bound holds on every run for every table w : Fin n → Fin n → ℝ; reason: the worst-case count never depends on the honesty of w; it specializes to w = weakDist d C adv
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.33, p.26 (PDF 27); proof pp.26–27

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

/-- **Lemma 3.33** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.26, PDF p.27; proof pp.26–27).
"Fix a guess λ > 0. With high probability, if the run completes sampling, rounding, repair, and
compression without aborting, it returns at most k balls and a valid assignment of all points. If
λ ≥ OPT/(2k), then, with high probability, the run does not abort and its total radius is O(kλ).
More precisely, if λ ≥ OPT/(2k) and the guarantees of Lemmas 3.17 and 3.21 hold, then for
0 < ϵ ≤ 1 the total radius is less than 2158kλ, so it is at most Ckλ for the fixed constant
C := 3000."

There is an absolute `c₀` such that for every `c ≥ c₀` there are `a > 0` and `n₀` with: for every
`δ ∈ (0, 1/2)`, `n ≥ n₀`, `k ≥ 1`, metric `d`, adversary, guess `λ > 0`, LP routine returning
optimal solutions, `ε ∈ (0, 1]` and offline routine with guarantee `(3 + ε)`:
1. with probability at least `1 − n^{−a}`, the test either aborts or returns a valid solution
   (at most `k` balls, every point in the ball of its slot);
2. if `λ ≥ OPT/(2k)`, with probability at least `1 − n^{−a}` the test does not abort and returns a
   valid solution of total radius less than `2158kλ`;
3. on every weak table and every run that completes repair, if `λ ≥ OPT/(2k)` and the selected
   family has total radius below `51kλ` (the guarantee of Lemma 3.17), the compressed solution has
   total radius less than `2158kλ`.

**Formalization Note.** `O(kλ)` in sentence 2 is the explicit `2158kλ` of sentence 3. In clause 3
the guarantees of Lemma 3.21 are not assumed (the cost bound does not use them). -/
theorem lemma_3_33 :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ,
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k →
    ∀ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d → ∀ adv : Adversary n,
    ∀ lam : ℝ, 0 < lam → ∀ sel : LPSelector n, SelectsOptimal sel →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ off : OfflineRoutine n k, GoodOffline d ε off →
      ENNReal.ofReal (1 - (n : ℝ) ^ (-a)) ≤
        jointProb δ (fun C => testLaw c δ k lam sel off d (weakDist d C adv))
          (fun _ t => ∀ s, t.result = some s → ValidSolution d s.σ s.ctr s.rad) ∧
      (MinSumRadiiPTAS.Main.msrOpt d k / (2 * k) ≤ lam →
        ENNReal.ofReal (1 - (n : ℝ) ^ (-a)) ≤
          jointProb δ (fun C => testLaw c δ k lam sel off d (weakDist d C adv))
            (fun _ t => ∃ s, t.result = some s ∧ ValidSolution d s.σ s.ctr s.rad ∧
              solCost s.rad < 2158 * k * lam)) ∧
      (∀ (w : Fin n → Fin n → ℝ), ∀ o ∈ (sampleLaw c k (hParam c δ n) lam sel d w).support,
        ∀ r : RoundOut n, round c k (hParam c δ n) lam d o.S.toFinset o.cands = .ok r →
        ∀ rp ∈ (repairLaw c k (hParam c δ n) (1 / 2 - δ) d w r).support, rp.aborted = false →
        MinSumRadiiPTAS.Main.msrOpt d k / (2 * k) ≤ lam →
        ((selectedFamily d o.S.toFinset o.cands lam (hParam c δ n)).map Cand.R).sum <
          51 * k * lam →
        solCost (compress r rp off).rad < 2158 * k * lam) := by sorry

end WeakStrongMSR
