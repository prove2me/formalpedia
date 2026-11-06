-- Prove2me | Theorems.Thm_ParetoNCSched_theorem_1_1
-- name    : ParetoNCSched.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:22:08.696512+00:00
-- url     : https://prove2.me/theorems/d16ad1ce-004d-4643-943b-d7ef1baf6cd4
-- title:
--   Theorem 1.1 — $\mathrm{MRC}_R$ is $R$-robust and $c(R)$-consistent for every $R>2$
-- statement:
--   Let $R>2$ and
--   $$c(R)=R\left(1-\left(1-\frac{R+2}{R^2}\right)^{\frac{R}{R+2}}\right). \tag{1}$$
--   The Maximal Robust Commitment algorithm $\mathrm{MRC}_R$ (Algorithm 1) for non-clairvoyant single-machine scheduling with a predicted order, minimizing the total completion time, is
--
--   1. $R$-robust: for every number of jobs $n$, every vector of sizes $p\in(0,\infty)^n$ and every predicted order $\sigma$, $\mathrm{MRC}_R(p,\sigma)\le R\cdot\mathrm{OPT}(p)$;
--   2. $c(R)$-consistent: for every $n$, every $p\in(0,\infty)^n$ and every correct predicted order $\sigma$ (that is, $p_{\sigma(1)}\le\cdots\le p_{\sigma(n)}$), $\mathrm{MRC}_R(p,\sigma)\le c(R)\cdot\mathrm{OPT}(p)$.
--
--   Here $\mathrm{MRC}_R(p,\sigma)$ is the total completion time of the run of $\mathrm{MRC}_R$ and $\mathrm{OPT}(p)$ the optimal total completion time over all preemptive schedules. With the matching lower bound of the paper (Theorem 1.2, not part of this mission), $c(R)$ is the best consistency of a deterministic $R$-robust algorithm.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the run of MRC_R as described by Algorithm 1 and the interval-by-interval construction (p.17) → iteration of a one-step map with explicit event candidates; the level as the minimum elapsed time of the waiting jobs; "pᵢ ≠ eⱼ(t_k)" as "pᵢ > eⱼ(t_k)"; rate function r_k on [t_k, t_{k+1}); reason: the same run: eⱼ and ℓ only increase, and Lemma B.1 makes the waiting jobs share one elapsed time
--   - encoding: real completion times and costs → completion times and costs in [0, ∞], Cⱼ = ∞ for a job that never completes; reason: same values on every run that completes; a run that does not finish has infinite cost, never a junk value
--   - encoding: OPT(p), the optimal total completion time → the infimum of Σⱼ Cⱼ over all measurable rate schedules (`IsSchedule`), in [0, ∞]; reason: this is the meaning of "optimal total completion time" for the schedules of Appendix A; the paper evaluates it by Smith's rule, a separate milestone; conditions imposed at every real t, with Borel measurable rates: a schedule on [0, ∞) extends by 0 and changes on a null set only, so the set of costs is the paper's
--   - encoding: rob / cons as suprema over n ≥ 1 of the ratio to OPT → the pointwise bound cost ≤ c · OPT for every n, p, σ (n = 0 included, both sides 0); reason: OPT(p) is positive and finite for n ≥ 1, so the supremum is ≤ c iff every ratio is; n = 0 is the excluded undefined 0/0 case
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 1.1, Theorem 1.1, Eq. (1), p.4 (proved as Theorems C.1, p.20, and D.6, p.30)

import Mathlib
import Definitions.Def_ParetoNCSched_mrcCost
import Definitions.Def_ParetoNCSched_OPT
import Definitions.Def_ParetoNCSched_IsCorrect
import Definitions.Def_ParetoNCSched_cR
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Theorem 1.1 (Upper bound).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 1.1, Theorem 1.1, p.4: "For every R > 2, MRC_R is R-robust
and c(R)-consistent, where c(R) = R(1 − (1 − (R + 2)/R²)^(R/(R+2))). (1)"

**Formalization Note.** `rob(MRC_R) ≤ R` and `cons(MRC_R) ≤ c(R)` (suprema over `n ≥ 1` of the ratio
to `OPT`, Appendix A, p.15) are stated pointwise: for every `n`, every `p > 0`, every predicted order
`σ` (robustness), resp. every correct `σ` (consistency), `MRC_R(p, σ) ≤ R · OPT(p)`, resp.
`≤ c(R) · OPT(p)`. `MRC_R(p, σ)` is the total completion time of the defined run of Algorithm 1
(`mrcCost`), `OPT(p)` the infimum over all preemptive schedules, both in `ℝ≥0∞`. -/
theorem theorem_1_1 (R : ℝ) (hR : 2 < R) :
    (∀ (n : ℕ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), (∀ j, 0 < p j) →
        mrcCost R p σ ≤ ENNReal.ofReal R * OPT p) ∧
    (∀ (n : ℕ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), (∀ j, 0 < p j) → IsCorrect p σ →
        mrcCost R p σ ≤ ENNReal.ofReal (cR R) * OPT p) := by sorry

end ParetoNCSched
