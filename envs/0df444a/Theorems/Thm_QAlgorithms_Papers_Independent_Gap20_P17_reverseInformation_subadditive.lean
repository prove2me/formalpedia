-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_reverseInformation_subadditive
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.reverseInformation_subadditive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:37:16.382743+00:00
-- url     : https://prove2.me/theorems/d72076f4-bb85-4043-bcb4-6246fb0f7106
-- title:
--   Reverse information on correlated two-use inputs
-- statement:
--   All registers are finite. A physical channel is completely positive and trace preserving; its fixed Stinespring isometry $V:A\to B\otimes E$ defines the receiver channel $\Lambda$ and its complementary channel $\Lambda^c$. Inputs $\rho$ are positive semidefinite of trace one. Entropies are in bits. Write $I(\Lambda,\rho)=S(\Lambda(\rho))-S(\Lambda^c(\rho))$ and $I_R(\Lambda,\rho)=S(\rho)-S(\Lambda^c(\rho))$. These equal the purified-reference definitions, with the reference retained by Alice. Let $\rho_{A_1A_2}$ be any density matrix, with marginals $\rho_{A_1}$ and $\rho_{A_2}$, and apply the same memoryless channel to both factors. Then
--
--   $$I_R(\Lambda\otimes\Lambda,\rho_{A_1A_2})\le I_R(\Lambda,\rho_{A_1})+I_R(\Lambda,\rho_{A_2}).$$
--
--   This is the correlated-input inequality used to establish single-letter reverse information.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 3, Eq.(7)

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

/-- PDF p.3, Eq.(7): same-channel subadditivity holds on every correlated input;
the two terms use the actual reduced input density matrices. -/
theorem reverseInformation_subadditive {a b e : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : IsIsometry V)
    (rho : Matrix (Fin a × Fin a) (Fin a × Fin a) ℂ) (hrho : IsDensityMatrix rho) :
    reverseInfo (productDilation V V) rho ≤
      reverseInfo V (traceRight rho) + reverseInfo V (traceLeft rho) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
