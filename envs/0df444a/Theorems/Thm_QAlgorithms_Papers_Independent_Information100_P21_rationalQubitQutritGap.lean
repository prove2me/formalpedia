-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_rationalQubitQutritGap
-- name    : QAlgorithms.Papers.Independent.Information100.P21.rationalQubitQutritGap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:12:00.683305+00:00
-- url     : https://prove2.me/theorems/8e4416f8-edb2-44eb-aafa-78f72d8b68ff
-- title:
--   IX.A–B — explicit full-rank 2 x 3 gap and certificates
-- statement:
--   Let $\rho_*$ be the literal rational S134 matrix. Set $u=2|01\rangle+|10\rangle$, $Y_g=|u\rangle\langle u|/40$, $W=(2/3)(|v_1\rangle\langle v_1|+|v_2\rangle\langle v_2|)$ for $v_1=|00\rangle+|11\rangle$, $v_2=|01\rangle+|12\rangle$, and $Z=W^\Gamma$. The input and target $S=\rho_*+Y_g$ are positive definite, $S$ is separable, and $\operatorname{Tr}Y_g=1/8$. The normalized noise is entangled. Both $W,Z$ have expectations in $[0,1]$ on arbitrary unit complex product vectors; $Z$ therefore bounds all separable states. Further, $WS^\Gamma=0$, $-\operatorname{Tr}(Z\rho_*)=2/15$, $\langle u|Z|u\rangle/\|u\|^2=16/15$, and the Rayleigh maximum of $Z$ is $(1+\sqrt5)/3>1$. Thus
--   $$R_g(\rho_*)\le1/8<2/15\le R_s(\rho_*),\qquad R_s(\rho_*)-R_g(\rho_*)\ge1/120.$$
--   Neither certificate is asserted optimal.
--
--   PDF p.25, S139: retain PPT and the spectrum 0,0,4,10,13,18 of 40 times the partially transposed target.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 2, IX.A–B — explicit full-rank 2 x 3 gap and certificates

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 2, explicit full-rank 2 x 3 gap and certificates.
Round-one coverage restoration: PDF p.25, S139: retain PPT and the spectrum 0,0,4,10,13,18 of 40 times the partially transposed target. -/
theorem rationalQubitQutritGap  :
  QAlgorithms.IsDensityMatrix rhoStar ∧ rhoStar.PosDef ∧ noiseStar.PosSemidef ∧
  noiseStar.trace.re=1/8 ∧ (rhoStar+noiseStar).PosDef ∧
  (pt (rhoStar+noiseStar)).PosSemidef ∧
  ((40 : ℂ) • pt (rhoStar+noiseStar)).charpoly =
    Polynomial.X^2 * (Polynomial.X - Polynomial.C (4 : ℂ)) *
    (Polynomial.X - Polynomial.C (10 : ℂ)) *
    (Polynomial.X - Polynomial.C (13 : ℂ)) *
    (Polynomial.X - Polynomial.C (18 : ℂ)) ∧
  QAlgorithms.Entanglement.IsSeparablePositive (rhoStar+noiseStar) ∧
  QAlgorithms.IsDensityMatrix ((1/5:ℂ) • proj noiseKet) ∧ ¬sep ((1/5:ℂ) • proj noiseKet) ∧
  witnessW.PosSemidef ∧ witnessZ.IsHermitian ∧
  (∀ (a : Vec (Fin 2)) (b : Vec (Fin 3)), ‖a‖=1 → ‖b‖=1 →
    0≤quad witnessW (tensor a b) ∧ quad witnessW (tensor a b)≤1 ∧
    0≤quad witnessZ (tensor a b) ∧ quad witnessZ (tensor a b)≤1) ∧
  (∀ sigma : Op QT, sep sigma → 0≤(witnessZ*sigma).trace.re ∧ (witnessZ*sigma).trace.re≤1) ∧
  witnessW*pt (rhoStar+noiseStar)=0 ∧ -(witnessZ*rhoStar).trace.re=2/15 ∧
  quad witnessZ noiseKet/‖noiseKet‖^2=16/15 ∧ ¬(1-witnessZ).PosSemidef ∧
  IsGreatest {q : ℝ | ∃ v : Vec QT, ‖v‖=1 ∧ q=quad witnessZ v} ((1+Real.sqrt 5)/3) ∧
  rg rhoStar≤1/8 ∧ (2/15:ℝ)≤rs rhoStar ∧ 1/120≤rs rhoStar-rg rhoStar := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
