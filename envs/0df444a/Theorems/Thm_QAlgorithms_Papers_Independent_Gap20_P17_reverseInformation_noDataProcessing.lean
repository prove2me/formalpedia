-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_reverseInformation_noDataProcessing
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.reverseInformation_noDataProcessing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:38:55.379989+00:00
-- url     : https://prove2.me/theorems/fa1eff75-9315-4f0c-bb2b-a7a70a9bf7e7
-- title:
--   Output processing can increase reverse coherent information
-- statement:
--   All registers are finite. A physical channel is completely positive and trace preserving; its fixed Stinespring isometry $V:A\to B\otimes E$ defines the receiver channel $\Lambda$ and its complementary channel $\Lambda^c$. Inputs $\rho$ are positive semidefinite of trace one. Entropies are in bits. Write $I(\Lambda,\rho)=S(\Lambda(\rho))-S(\Lambda^c(\rho))$ and $I_R(\Lambda,\rho)=S(\rho)-S(\Lambda^c(\rho))$. These equal the purified-reference definitions, with the reference retained by Alice. There exist a qubit channel $\Lambda$ with a four-dimensional dilation environment, a qubit postprocessing channel $\mathcal M$ with a two-dimensional environment, and a density input $\rho$, such that
--
--   $$I_R(\mathcal M\circ\Lambda,\rho)>I_R(\Lambda,\rho).$$
--
--   Both channels are physical isometric dilations; the composite retains both environments. This witnesses failure of a universal output data-processing law, without claiming failure for every channel.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 3, paragraph following Eq.(7)

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

/-- PDF p.3: failure of a universal output data-processing inequality, stated as
existence of two physical channels and a normalized input witnessing an increase. -/
theorem reverseInformation_noDataProcessing :
    ∃ V : Matrix (Fin 2 × Fin 4) (Fin 2) ℂ,
    ∃ W : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ,
    ∃ rho : Matrix (Fin 2) (Fin 2) ℂ,
      IsIsometry V ∧ IsIsometry W ∧ IsDensityMatrix rho ∧
      reverseInfo V rho < reverseInfo (composeDilation V W) rho := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
