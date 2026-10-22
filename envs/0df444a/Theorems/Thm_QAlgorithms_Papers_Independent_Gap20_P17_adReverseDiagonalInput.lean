-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_adReverseDiagonalInput
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.adReverseDiagonalInput
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:48:33.224131+00:00
-- url     : https://prove2.me/theorems/297a9434-2925-497a-a07b-e6d5dfb8d003
-- title:
--   Fixed-population diagonal reverse optimizer for AD
-- statement:
--   Let $\eta,p\in[0,1]$, $\theta\in[0,\pi]$, and $\phi\in\mathbb R$. For the qubit input with diagonal $(1-p,p)$ and upper off-diagonal $\sqrt{(1-p)p}e^{-i\phi}\cos\theta$,
--
--   $$I_R(D_\eta,\rho(p,\theta,\phi))\le I_R(D_\eta,\operatorname{diag}(1-p,p)).$$
--
--   This fixed-population reverse optimum applies throughout the physical survival interval, including degenerate equality cases.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 6, appendix reverse-coherent-information optimization

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

/-- PDF p.6: fixed-population reverse-information optimality for every physical
AD survival parameter, including equality regimes. No forward threshold is imported. -/
theorem adReverseDiagonalInput (eta p theta phi : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    reverseInfo (adDilation eta) (generalInput p theta phi) ≤
      reverseInfo (adDilation eta) (diagonalInput p) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
