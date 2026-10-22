-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_adForwardDiagonalInput
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.adForwardDiagonalInput
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:47:46.176037+00:00
-- url     : https://prove2.me/theorems/63770bd7-4fba-4ddc-abe8-9c5048a33d91
-- title:
--   Fixed-population diagonal forward optimizer for degradable AD
-- statement:
--   Let $1/2<\eta\le1$, $p\in[0,1]$, $\theta\in[0,\pi]$, and $\phi\in\mathbb R$. Let $\rho(p,\theta,\phi)$ have diagonal $(1-p,p)$ and upper off-diagonal $\sqrt{(1-p)p}e^{-i\phi}\cos\theta$. For physical qubit amplitude damping,
--
--   $$I(D_\eta,\rho(p,\theta,\phi))\le I(D_\eta,\operatorname{diag}(1-p,p)).$$
--
--   Thus dephasing maximizes coherent information at each fixed population in the degradable regime used by the source's proof.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 5, appendix coherent-information optimization

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

/-- PDF p.5: at fixed excited population, a diagonal input maximizes forward
information for degradable AD, in the eta>1/2 regime explicitly used by the proof. -/
theorem adForwardDiagonalInput (eta p theta phi : ℝ)
    (heta : eta ∈ Set.Ioc (1/2 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    forwardInfo (adDilation eta) (generalInput p theta phi) ≤
      forwardInfo (adDilation eta) (diagonalInput p) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
