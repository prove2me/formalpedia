-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_discrete_ensemble_barycenter
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.discrete_ensemble_barycenter
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:18:43.259735+00:00
-- url     : https://prove2.me/theorems/53ee2334-9efa-4a05-ac75-23121e628bd3
-- title:
--   Remark 3 (discrete barycenters and channel pushforwards)
-- statement:
--   Let $p_i\ge0$ be a countable probability list with $\sum_i p_i=1$ and let $\rho_i$ be normalized trace-class states. The measure $\mu=\sum_i p_i\delta_{\rho_i}$ is a probability ensemble and has a state barycenter
--
--   $$\bar\rho=\sum_i p_i\rho_i.$$
--
--   The coefficient series are summable and equal the integrable coefficients of that barycenter. For every CPTP trace-class channel $\Phi$, its state action is measurable and
--
--   $$\Phi_*\mu=\sum_i p_i\delta_{\Phi(\rho_i)}.$$
--
--   Zero weights and coincident atoms are allowed. This identifies the actual countable atomic laws and barycenters used for discrete constrained capacities.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 43, Remark 3 (discrete barycenters and channel pushforwards)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P46

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Bridge50.P23 (energyMagnitude numberEnergy)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize rankOne tensorApply productCoeff IsBarycenter)

attribute [local instance] Classical.propDecidable Classical.decEq

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Remark 3, PDF pp.43--44: a genuine countable atomic law, its normalized
barycenter with convergent coefficients, and its channel pushforward. -/
theorem discrete_ensemble_barycenter {I J : Type} [Countable I] [Infinite I]
    [Countable J] [Infinite J] (e : Spectral.CountableStateEnsemble I)
    (Phi : Spectral.Channel I J) :
    IsProbabilityMeasure (discreteLaw e) ∧
    ∃ rho : State I, Spectral.Barycenter e rho.coefficients ∧
      IsBarycenter (discreteLaw e) State.coefficients rho.coefficients ∧
      (∀ i j, Summable (fun n =>
        ((e.weight n).toReal : ℂ) * (e.state n).coefficients i j)) ∧
      ∃ output : State I → State J,
        (∀ sigma, (output sigma).coefficients = Phi.val sigma.coefficients) ∧
        Measurable output ∧
        Measure.map output (discreteLaw e) =
          Measure.sum (fun n => e.weight n • Measure.dirac (output (e.state n))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
