-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_gadReverseDiagonalInput
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.gadReverseDiagonalInput
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:52:43.172998+00:00
-- url     : https://prove2.me/theorems/b3aeadf4-46a3-4dc1-8ea2-d4dc57042d40
-- title:
--   Fixed-population diagonal reverse optimizer for GAD
-- statement:
--   Let $\eta,\alpha,p\in[0,1]$, $\theta\in[0,\pi]$, and $\phi\in\mathbb R$. For the input with diagonal $(1-p,p)$ and upper off-diagonal $\sqrt{(1-p)p}e^{-i\phi}\cos\theta$, the physical thermal GAD channel satisfies
--
--   $$I_R(D_{\eta,\alpha},\rho(p,\theta,\phi))\le I_R(D_{\eta,\alpha},\operatorname{diag}(1-p,p)).$$
--
--   This diagonal reverse optimum is at fixed population and includes all equality regimes. It follows the source's input-optimality claim, rather than its unqualified count of extrema.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 7, appendix opening p.4 and reverse reconciliation pp.7–8

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

/-- PDF pp.4,7–8: fixed-population diagonal reverse optimizer for GAD, including
non-strict equality cases; Fig.9 is illustrative rather than a universal survey. -/
theorem gadReverseDiagonalInput (eta alpha p theta phi : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    reverseInfo (gadDilation eta alpha) (generalInput p theta phi) ≤
      reverseInfo (gadDilation eta alpha) (diagonalInput p) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
