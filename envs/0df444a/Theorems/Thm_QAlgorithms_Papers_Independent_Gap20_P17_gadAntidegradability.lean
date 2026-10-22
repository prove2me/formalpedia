-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_gadAntidegradability
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.gadAntidegradability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:46:28.248112+00:00
-- url     : https://prove2.me/theorems/ddf03a0a-7291-449a-8275-8b7eea5ea0f0
-- title:
--   GAD antidegradability and zero unassisted capacity at high damping
-- statement:
--   Let $0\le\eta\le1/2$ and $0\le\alpha\le1$. Use the physical thermal generalized amplitude-damping channel $D_{\eta,\alpha}$ and its normalized pure Stinespring dilation, whose complete environment has dimension four. Then
--
--   $$\exists\mathcal G:E\to B\text{ CPTP},\qquad D_{\eta,\alpha}=\mathcal G\circ D_{\eta,\alpha}^c,\qquad E(D_{\eta,\alpha})=0.$$
--
--   The equality holds on all operators. It expresses antidegradability without applying a qubit-to-qubit map directly to the four-dimensional complement.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 4, antidegradability paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4: existence of a CPTP antidegrading map for the full four-dimensional
GAD complement and zero unassisted entanglement capacity. The printed qubit map
on rho_E suppresses subsystems. The separate signed reverse-information
nonnegativity claim is deferred; no clipping convention is imposed here. -/
theorem gadAntidegradability (eta alpha : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) (1/2)) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1) :
    IsAntidegradable (gadDilation eta alpha) ∧
    entanglementCapacity (gadChannel eta alpha) .unassisted = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
