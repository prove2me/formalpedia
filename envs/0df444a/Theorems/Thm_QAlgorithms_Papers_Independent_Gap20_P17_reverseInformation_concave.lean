-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_reverseInformation_concave
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.reverseInformation_concave
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:49:28.706494+00:00
-- url     : https://prove2.me/theorems/41d9083c-59f6-4e5d-9277-9a532475fd89
-- title:
--   Concavity of reverse channel information
-- statement:
--   All registers are finite. A physical channel is completely positive and trace preserving; its fixed Stinespring isometry $V:A\to B\otimes E$ defines the receiver channel $\Lambda$ and its complementary channel $\Lambda^c$. Inputs $\rho$ are positive semidefinite of trace one. Entropies are in bits. Write $I(\Lambda,\rho)=S(\Lambda(\rho))-S(\Lambda^c(\rho))$ and $I_R(\Lambda,\rho)=S(\rho)-S(\Lambda^c(\rho))$. These equal the purified-reference definitions, with the reference retained by Alice. For any two density inputs $\rho,\sigma$ and $t\in[0,1]$,
--
--   $$I_R(\Lambda,t\rho+(1-t)\sigma)\ge tI_R(\Lambda,\rho)+(1-t)I_R(\Lambda,\sigma).$$
--
--   This is concavity for every channel. Diagonal-input conclusions require the additional phase covariance of the named damping channels.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 4, appendix preamble

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

/-- PDF p.4, appendix preamble: reverse channel information is concave on all
normalized density inputs for every physical finite-dimensional channel. -/
theorem reverseInformation_concave {a b e : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : IsIsometry V)
    (rho sigma : Matrix (Fin a) (Fin a) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t*reverseInfo V rho + (1-t)*reverseInfo V sigma ≤
      reverseInfo V ((t : ℂ) • rho + ((1-t : ℝ) : ℂ) • sigma) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
