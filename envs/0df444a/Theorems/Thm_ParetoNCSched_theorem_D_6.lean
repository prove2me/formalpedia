-- Prove2me | Theorems.Thm_ParetoNCSched_theorem_D_6
-- name    : ParetoNCSched.theorem_D_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:22:20.327404+00:00
-- url     : https://prove2.me/theorems/a1683426-f67b-4e9f-969a-933ed6a4e231
-- title:
--   Theorem D.6 — consistency: $\mathrm{MRC}_R\le c(R)\,\mathrm{OPT}$ on a correct order
-- statement:
--   Let $R>2$ and let $c(R)$ be given by (1). For every instance $p\in(0,\infty)^n$ and every correct predicted order $\sigma$,
--   $$\mathrm{MRC}_R(p,\sigma)\le c(R)\cdot\mathrm{OPT}(p).$$
--
--   This is the consistency half of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the run of MRC_R as described by Algorithm 1 and the interval-by-interval construction (p.17) → iteration of a one-step map with explicit event candidates; the level as the minimum elapsed time of the waiting jobs; "pᵢ ≠ eⱼ(t_k)" as "pᵢ > eⱼ(t_k)"; rate function r_k on [t_k, t_{k+1}); reason: the same run: eⱼ and ℓ only increase, and Lemma B.1 makes the waiting jobs share one elapsed time
--   - encoding: real completion times and costs → completion times and costs in [0, ∞], Cⱼ = ∞ for a job that never completes; reason: same values on every run that completes; a run that does not finish has infinite cost, never a junk value
--   - encoding: OPT(p), the optimal total completion time → the infimum of Σⱼ Cⱼ over all measurable rate schedules (`IsSchedule`), in [0, ∞]; reason: this is the meaning of "optimal total completion time" for the schedules of Appendix A; the paper evaluates it by Smith's rule, a separate milestone; conditions imposed at every real t, with Borel measurable rates: a schedule on [0, ∞) extends by 0 and changes on a null set only, so the set of costs is the paper's
--   - encoding: rob / cons as suprema over n ≥ 1 of the ratio to OPT → the pointwise bound cost ≤ c · OPT for every n, p, σ (n = 0 included, both sides 0); reason: OPT(p) is positive and finite for n ≥ 1, so the supremum is ≤ c iff every ratio is; n = 0 is the excluded undefined 0/0 case
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem D.6, p.30

import Mathlib
import Definitions.Def_ParetoNCSched_mrcCost
import Definitions.Def_ParetoNCSched_OPT
import Definitions.Def_ParetoNCSched_IsCorrect
import Definitions.Def_ParetoNCSched_cR
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Theorem D.6 (Consistency of MRC_R).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, Theorem D.6, p.30: "Let R > 2 and let c(R)
be given by (1). If σ is correct, then MRC_R ≤ c(R) OPT."

**Formalization Note.** For every number of jobs `n`, sizes `p > 0` and correct order `σ`. -/
theorem theorem_D_6 (R : ℝ) (hR : 2 < R) {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (σ : Equiv.Perm (Fin n)) (hσ : IsCorrect p σ) :
    mrcCost R p σ ≤ ENNReal.ofReal (cR R) * OPT p := by sorry

end ParetoNCSched
