-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_bsaRemainder
-- name    : QAlgorithms.Papers.Independent.Information100.P21.bsaRemainder
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:57:05.659448+00:00
-- url     : https://prove2.me/theorems/8b569811-e07f-448d-9039-6155b85b38f7
-- title:
--   VI.18 — Proposition VI.18 (Parity and robustness noise of the BSA remainder). If ρX lies in the w-entangled branch, then
-- statement:
--   Take a pure-remainder best separable approximation $\rho_X=S+\varepsilon|\psi\rangle\langle\psi|$, with unit $\psi$, $\varepsilon>0$, and maximal separable weight $\operatorname{Tr}S$. In the entangled $w$ branch, up to global phase,
--   $$\psi=\alpha|00\rangle+e^{i\phi}\beta|11\rangle,\quad\alpha,\beta>0,\quad\alpha^2+\beta^2=1.$$
--   For the pure remainder, $R_s=R_g=2\alpha\beta$, and the equal mixture of $|01\rangle,|10\rangle$ is optimal separable noise. In the $z$ branch the remainder has odd parity and the noise pair is $|00\rangle,|11\rangle$. These costs belong to the pure remainder, not the original mixed state.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 21, VI.18 — Proposition VI.18 (Parity and robustness noise of the BSA remainder). If ρX lies in the w-entangled branch, then

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 21, Proposition VI.18 (Parity and robustness noise of the BSA remainder). If ρX lies in the w-entangled branch, then. -/
theorem bsaRemainder (a b c d w z : ℝ) (h : physicalX a b c d w z)
  (S : Op QQ) (epsilon : ℝ) (psi : Vec QQ) (hB : pureBSA (xstate a b c d w z) S epsilon psi) :
  ∀ odd : Bool, (if odd then b*c<w^2 else a*d<z^2) →
  ∃ alpha beta phi : ℝ, 0<alpha ∧ 0<beta ∧ alpha^2+beta^2=1 ∧
    proj psi=proj ((alpha:ℂ) • QAlgorithms.ket (0, if odd then 0 else 1) +
      (Complex.exp (Complex.I*(phi:ℂ))*(beta:ℂ)) • QAlgorithms.ket (1, if odd then 1 else 0)) ∧
    rs (proj psi)=2*alpha*beta ∧ rg (proj psi)=2*alpha*beta ∧
    sep (compressed odd (1/2) (1/2)) ∧ QAlgorithms.IsDensityMatrix (compressed odd (1/2) (1/2)) ∧
    sep (mix (proj psi) (compressed odd (1/2) (1/2)) (2*alpha*beta)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
