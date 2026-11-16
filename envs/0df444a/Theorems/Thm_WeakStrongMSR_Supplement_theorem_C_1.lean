-- Prove2me | Theorems.Thm_WeakStrongMSR_Supplement_theorem_C_1
-- name    : WeakStrongMSR.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:36:00.144095+00:00
-- url     : https://prove2.me/theorems/8696fcf4-cf2d-4815-95f8-d99f73cfd09f
-- title:
--   Theorem C.1 — with $\epsilon=1/100$ and $c\ge 20000$ the algorithm returns a valid solution of total radius $<270\,\mathrm{OPT}$ w.h.p.
-- statement:
--   There is an absolute constant $c_0$ such that for every integer constant $c\ge\max(c_0,20000)$ there is $a>0$, and for every exponent $e$ there is $n_0$, with the following property. Let $\delta\in(0,\tfrac12)$, $n\ge n_0$, $1\le k<n$, let $d$ be a metric on $n$ points (distinct points at positive distance), let $\Delta$ be a known bound on its aspect ratio with $\mathrm{aspect}(d)\le\Delta\le n^e$, and fix any adversary. Run the algorithm of the main result (binary search over the guesses, Algorithm 5, with the parameters of Appendix A) with an LP routine that returns optimal solutions and an offline routine with approximation guarantee $3+\epsilon$ for $\epsilon=1/100$. Then, with probability at least $1-n^{-a}$ over the corruptions and the algorithm's coins, it returns a valid solution (nonnegative radii, every point assigned to a ball containing it) whose total radius satisfies
--   $$\sum_j r_j\ <\ 270\cdot\mathrm{OPT}.$$
--
--   This makes the constant of Theorem 1.2 explicit: the approximation factor of the algorithm is less than $270$, for every $\delta$.
--
--   **Formalization Note** The algorithm is the published `WeakStrongMSR.guessLaw`; the hypotheses on the LP and offline routines and on $\Delta$, and the quantifier order, are those of the published Lemma 3.37 (which gives $3000\cdot\mathrm{OPT}$). The heaviness threshold and $\xi=1/1000$ of the proof are devices of the analysis and do not appear.
--
--   Differences from the source:
--   - reading: "a constant $c\ge 20000$", where $c$ is "a sufficiently large absolute constant, fixed in the analysis" (§2.3, p.5; App. A, p.34) → $\exists c_0$ such that every $c\ge c_0$ with $c\ge 20000$; reason: the algorithm's $c$ is sufficiently large in every result of the analysis by the standing assumption of §2.3 and App. A; C.1's proof re-checks only the sampling step at $c\ge20000$ and uses Lemmas 3.17 and 3.33 for the rest
--   - reading: "with high probability", "the algorithm of Theorem 3.35, run with the parameters of Section A" → probability at least $1-n^{-a}$ with $a>0$ chosen after $c$ and before $e,\delta,n$, for $n\ge n_0$; the published `guessLaw` with an optimal LP routine, a $(3+1/100)$ offline routine and a known bound $\mathrm{aspect}(d)\le\Delta\le n^e$; reason: the reading of the published goal and Lemma 3.37 (§2.3: the aspect-ratio bound is known and polynomial)
--   - encoding: $k<n$ → $1\le k<n$; reason: for $k=0$ and $n\ge1$ there is no solution at all; MSR has $k\ge1$ throughout the paper
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Theorem C.1, p.37 (PDF 38); proof pp.37–38; parameters App. A, p.34 (PDF 35)

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

namespace WeakStrongMSR.Supplement

open WeakStrongMSR

/-- **Theorem C.1** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong
and Weak Oracles*, manuscript, sha256 5f8fbaf3…67e8f92a0, p.37, PDF p.38; proof pp.37–38). "For
every constant δ ∈ (0, 1/2), k < n, offline parameter ϵ = 1/100 and a constant c ≥ 20000, with high
probability the algorithm of Theorem 3.35, run with the parameters of Section A, returns a solution
of total radius less than 270 OPT."

There is an absolute `c₀` such that for every `c ≥ c₀` with `c ≥ 20000` there is `a > 0`, and for
every aspect-ratio exponent `e` there is `n₀`, with: for every `δ ∈ (0, 1/2)`, `n ≥ n₀`,
`1 ≤ k < n`, metric `d`, aspect-ratio bound `Δ` with `aspect(d) ≤ Δ ≤ n^e`, adversary, LP routine
returning optimal solutions and offline routine with guarantee `3 + 1/100`, with probability at
least `1 − n^{−a}` over the corruption set and the algorithm's coins the search algorithm
(Algorithm 5 with the App. A parameters, `WeakStrongMSR.guessLaw`) returns a valid solution of
total radius less than `270 · OPT`.

**Formalization Note.** `c` is the algorithm's absolute constant; §2.3 and App. A ("c is a large
enough absolute constant, and it does not depend on δ") make it sufficiently large in every result
of the analysis, and C.1 adds `c ≥ 20000`. The quantifier order and the hypotheses on `sel`, `off`,
`Δ` are those of the published Lemma 3.37; only the offline parameter is fixed to `1/100` and the
cost bound is the strict `< 270 · OPT`. -/
theorem theorem_C_1 :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → 20000 ≤ c → ∃ a : ℝ, 0 < a ∧ ∀ e : ℕ, ∃ n₀ : ℕ,
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
    ∀ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d →
    ∀ Δ : ℝ, aspectRatio d ≤ Δ → Δ ≤ (n : ℝ) ^ e →
    ∀ adv : Adversary n, ∀ sel : LPSelector n, SelectsOptimal sel →
    ∀ off : OfflineRoutine n k, GoodOffline d (1 / 100) off →
      ENNReal.ofReal (1 - (n : ℝ) ^ (-a)) ≤
        jointProb δ (fun C => guessLaw c δ k Δ sel off d (weakDist d C adv))
          (fun _ g => ∃ s, g.sol = some s ∧ ValidSolution d s.σ s.ctr s.rad ∧
            solCost s.rad < 270 * MinSumRadiiPTAS.Main.msrOpt d k) := by sorry

end WeakStrongMSR.Supplement
