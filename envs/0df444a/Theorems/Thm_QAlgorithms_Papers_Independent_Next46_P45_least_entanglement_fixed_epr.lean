-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P45_least_entanglement_fixed_epr
-- name    : QAlgorithms.Papers.Independent.Next46.P45.least_entanglement_fixed_epr
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:49:33.101578+00:00
-- url     : https://prove2.me/theorems/b9444524-e3ee-4ea4-978e-be988d3acda5
-- title:
--   Least pure-state entanglement at fixed EPR uncertainty
-- statement:
--   Fix $0<\Delta<1$, put $r_\Delta=-\frac12\ln\Delta$, and let $\Psi_s(r_\Delta)$ be the normalized two-mode squeezed vector. Over all normalized pure states of the full two-oscillator Hilbert space, with extended entropy $E$ in bits and clipped EPR uncertainty $\Delta(\psi)$, one has
--
--   $$E\bigl(\Psi_s(r_\Delta)\bigr)=\inf_{\psi:\,\Delta(\psi)=\Delta}E(\psi).$$
--
--   The infimum is attained: $\|\Psi_s(r_\Delta)\|=1$ and $\Delta(\Psi_s(r_\Delta))=\Delta$. Variance is infinite outside the observable domain; infinite entropies are allowed in the constrained set. The explicit witness supplies nonemptiness and turns the lower bound into a minimum characterization.
-- source:
--   Entanglement of formation for symmetric Gaussian states, arXiv:quant-ph/0304042v1, PDF p. 2, Proposition 1, equivalent formulation (i): least entanglement at fixed EPR uncertainty

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne IsBarycenter)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance standardFormCovariance productWeyl
   CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits InterleavedPhase)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF p.2, equivalent formulation (i): constrained infimum and its explicit
attaining squeezed state; the level set is not assumed nonempty. -/
theorem least_entanglement_fixed_epr (delta : ℝ) (hdelta : 0 < delta) (hlt : delta < 1) :
    ‖squeezedVector (squeezingAt delta)‖ = 1 ∧
    eprUncertainty (squeezedVector (squeezingAt delta)) = delta ∧
    pureEntanglement (squeezedVector (squeezingAt delta)) =
      ⨅ psi : {psi : PureVector // eprUncertainty psi.val = delta}, pureEntanglement psi.val.val := by sorry

end QAlgorithms.Papers.Independent.Next46.P45

end
