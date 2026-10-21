-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P45_greatest_epr_correlation_fixed_entanglement
-- name    : QAlgorithms.Papers.Independent.Next46.P45.greatest_epr_correlation_fixed_entanglement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:50:12.027749+00:00
-- url     : https://prove2.me/theorems/db46b5d8-baaa-42a9-a20d-8637f3d21f34
-- title:
--   Greatest EPR correlation at fixed finite entanglement
-- statement:
--   For every finite real $E>0$, there exists $r>0$ such that the two-mode squeezed vector $\Psi_s(r)$ is normalized and $E(\Psi_s(r))=E$, where entanglement is reduced-state spectral entropy in bits. It also satisfies
--
--   $$\Delta(\Psi_s(r))=\inf_{\psi:\,E(\psi)=E}\Delta(\psi).$$
--
--   The infimum ranges over all normalized pure states of the full two-mode oscillator space, and $\Delta$ is the clipped sum of EPR variances, assigning infinite variance outside the observable domain before clipping. The displayed squeezed vector attains the infimum. This identifies maximal EPR correlation at each positive finite entanglement without claiming a unique minimizing vector or including $E=+\infty$.
-- source:
--   Entanglement of formation for symmetric Gaussian states, arXiv:quant-ph/0304042v1, PDF p. 2, Proposition 1, equivalent formulation (ii): greatest EPR correlation at fixed entanglement

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

/-- PDF p.2, equivalent formulation (ii): each finite positive entanglement E
selects an attaining squeezed state. No uniqueness of the minimizing vector. -/
theorem greatest_epr_correlation_fixed_entanglement (E : ℝ) (hE : 0 < E) :
    ∃ r : ℝ, 0 < r ∧ ‖squeezedVector r‖ = 1 ∧
      pureEntanglement (squeezedVector r) = ENNReal.ofReal E ∧
      ENNReal.ofReal (eprUncertainty (squeezedVector r)) =
        ⨅ psi : {psi : PureVector // pureEntanglement psi.val = ENNReal.ofReal E},
          ENNReal.ofReal (eprUncertainty psi.val.val) := by sorry

end QAlgorithms.Papers.Independent.Next46.P45

end
