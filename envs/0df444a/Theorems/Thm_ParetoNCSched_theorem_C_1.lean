-- Prove2me | Theorems.Thm_ParetoNCSched_theorem_C_1
-- name    : ParetoNCSched.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:23:51.962687+00:00
-- url     : https://prove2.me/theorems/60b264f5-4422-4b83-8f0f-fb80476107e6
-- title:
--   Theorem C.1 — robustness: $F(t)\le R\,\Phi(e(t))$ and $\mathrm{MRC}_R\le R\,\mathrm{OPT}$
-- statement:
--   Let $R\ge2$. For every instance $p\in(0,\infty)^n$ and every predicted order $\sigma$, the run of $\mathrm{MRC}_R$ satisfies
--   $$F(t)\le R\,\Phi(e(t))\qquad\text{for all } t\ge0,$$
--   and in particular
--   $$\mathrm{MRC}_R(p,\sigma)\le R\cdot\mathrm{OPT}(p),$$
--   that is, $\mathrm{rob}(\mathrm{MRC}_R)\le R$.
--
--   This is the robustness half of Theorem 1.1, valid for every $R\ge2$.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the run of MRC_R as described by Algorithm 1 and the interval-by-interval construction (p.17) → iteration of a one-step map with explicit event candidates; the level as the minimum elapsed time of the waiting jobs; "pᵢ ≠ eⱼ(t_k)" as "pᵢ > eⱼ(t_k)"; rate function r_k on [t_k, t_{k+1}); reason: the same run: eⱼ and ℓ only increase, and Lemma B.1 makes the waiting jobs share one elapsed time
--   - encoding: real completion times and costs → completion times and costs in [0, ∞], Cⱼ = ∞ for a job that never completes; reason: same values on every run that completes; a run that does not finish has infinite cost, never a junk value
--   - encoding: OPT(p), the optimal total completion time → the infimum of Σⱼ Cⱼ over all measurable rate schedules (`IsSchedule`), in [0, ∞]; reason: this is the meaning of "optimal total completion time" for the schedules of Appendix A; the paper evaluates it by Smith's rule, a separate milestone; conditions imposed at every real t, with Borel measurable rates: a schedule on [0, ∞) extends by 0 and changes on a null set only, so the set of costs is the paper's
--   - encoding: rob / cons as suprema over n ≥ 1 of the ratio to OPT → the pointwise bound cost ≤ c · OPT for every n, p, σ (n = 0 included, both sides 0); reason: OPT(p) is positive and finite for n ≥ 1, so the supremum is ≤ c iff every ratio is; n = 0 is the excluded undefined 0/0 case
--   - encoding: "for all t" → for all t ≥ 0; reason: time starts at 0 in the model (p.7)
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem C.1, p.20

import Mathlib
import Definitions.Def_ParetoNCSched_mrcCost
import Definitions.Def_ParetoNCSched_OPT
import Definitions.Def_ParetoNCSched_stateAt
import Definitions.Def_ParetoNCSched_Phi
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Theorem C.1 (Robustness for every prediction).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix C, Theorem C.1, p.20: "Let R ≥ 2.
For every instance and every permutation σ, MRC_R maintains F(t) ≤ R Φ(e(t)) for all t. In particular
rob(MRC_R) ≤ R."

**Formalization Note.** Time runs over `t ≥ 0`. "rob(MRC_R) ≤ R" is stated pointwise:
`MRC_R(p, σ) ≤ R · OPT(p)` for every instance and every σ (equivalent, as `OPT(p) > 0`). -/
theorem theorem_C_1 (R : ℝ) (hR : 2 ≤ R) {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Equiv.Perm (Fin n)) :
    (∀ t : ℝ, 0 ≤ t →
      costSoFar p (mrcRate R p σ) t ≤ R * Phi (fun i => elapsed (mrcRate R p σ) i t)) ∧
    mrcCost R p σ ≤ ENNReal.ofReal R * OPT p := by sorry

end ParetoNCSched
