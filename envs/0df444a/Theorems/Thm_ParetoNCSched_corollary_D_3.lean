-- Prove2me | Theorems.Thm_ParetoNCSched_corollary_D_3
-- name    : ParetoNCSched.corollary_D_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:29:11.73765+00:00
-- url     : https://prove2.me/theorems/8b30b28e-44a9-4823-b13d-5f4aa210995d
-- title:
--   Corollary D.3 — $\mathrm{MRC}_R=\mathrm{OPT}+\int_0^\infty\frac{U_s(U_s-1)}{2}ds$ on a correct order
-- statement:
--   Let $R\ge2$, $p\in(0,\infty)^n$ and let $\sigma$ be a correct order. Then
--   $$\mathrm{MRC}_R(p,\sigma)=\mathrm{OPT}(p)+\int_0^\infty\frac{U_s(U_s-1)}{2}\,ds. \tag{8}$$
--
--   The excess cost of $\mathrm{MRC}_R$ over the optimum on a correct order is exactly the Round-Robin overhead of the layers crossed together by the $U_s$ jobs still unfinished when the level reaches $s$.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and positions σ(1), …, σ(n) → jobs `Fin n`, 0-based positions, σ k the job at position k; reason: relabelling only; same instances
--   - encoding: the run of MRC_R as described by Algorithm 1 and the interval-by-interval construction (p.17) → iteration of a one-step map with explicit event candidates; the level as the minimum elapsed time of the waiting jobs; "pᵢ ≠ eⱼ(t_k)" as "pᵢ > eⱼ(t_k)"; rate function r_k on [t_k, t_{k+1}); reason: the same run: eⱼ and ℓ only increase, and Lemma B.1 makes the waiting jobs share one elapsed time
--   - encoding: real completion times and costs → completion times and costs in [0, ∞], Cⱼ = ∞ for a job that never completes; reason: same values on every run that completes; a run that does not finish has infinite cost, never a junk value
--   - encoding: OPT(p), the optimal total completion time → the infimum of Σⱼ Cⱼ over all measurable rate schedules (`IsSchedule`), in [0, ∞]; reason: this is the meaning of "optimal total completion time" for the schedules of Appendix A; the paper evaluates it by Smith's rule, a separate milestone; conditions imposed at every real t, with Borel measurable rates: a schedule on [0, ∞) extends by 0 and changes on a null set only, so the set of costs is the paper's
--   - encoding: the integral ∫₀^∞ U_s(U_s − 1)/2 ds → the lower Lebesgue integral in [0, ∞] over (0, ∞) of the nonnegative function U_s(U_s − 1)/2; reason: the integrand is nonnegative (U_s ∈ ℕ), so the lower integral is the paper's integral with no integrability side condition
--   - encoding: an instance of n jobs (the suprema of p.15 range over n ≥ 1) → every n : ℕ, n = 0 included; reason: with no jobs every clause is trivial or vacuous, so the case adds nothing and removes nothing
--   - encoding: N(t) = |{j : C_j > t}| (p.15) at a time t → #{i : eᵢ(t) < pᵢ}, the unfinished jobs of the state ⟨t, e(t), F(t)⟩ (`stateAt`); reason: p.17: a job is completed iff eᵢ = pᵢ; on the run eᵢ is continuous and non-decreasing, so eᵢ(t) < pᵢ iff Cᵢ > t
--   - encoding: "the relabelled instance" (σ the identity), job n and the level ℓ of Lemma D.1 → σ kept, job n written σ(n − 1), ℓ the function `levelD`; reason: relabelling only
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Corollary D.3, Eq. (8), p.23

import Mathlib
import Definitions.Def_ParetoNCSched_mrcCost
import Definitions.Def_ParetoNCSched_OPT
import Definitions.Def_ParetoNCSched_Us
import Definitions.Def_ParetoNCSched_IsCorrect
open scoped ENNReal
open MeasureTheory Set

namespace ParetoNCSched

/-- **Corollary D.3 (Cost of MRC_R).** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.1, Corollary D.3, (8), p.23: "Let R ≥ 2. On a
correct order, MRC_R = OPT + ∫₀^∞ U_s(U_s − 1)/2 ds."

**Formalization Note.** The integral of the nonnegative function `U_s(U_s − 1)/2` is the lower
Lebesgue integral in `ℝ≥0∞` over `(0, ∞)` (no integrability side condition, no junk value). -/
theorem corollary_D_3 (R : ℝ) (hR : 2 ≤ R) {n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Equiv.Perm (Fin n)) (hσ : IsCorrect p σ) :
    mrcCost R p σ = OPT p +
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((Us R p σ s : ℝ) * ((Us R p σ s : ℝ) - 1) / 2) := by sorry

end ParetoNCSched
