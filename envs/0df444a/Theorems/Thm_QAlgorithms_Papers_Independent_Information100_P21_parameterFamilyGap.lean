-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_parameterFamilyGap
-- name    : QAlgorithms.Papers.Independent.Information100.P21.parameterFamilyGap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:12:36.894911+00:00
-- url     : https://prove2.me/theorems/18783846-e179-4680-a92c-c60c65368f8d
-- title:
--   IX.B — open parameter family of strict gaps
-- statement:
--   Let $M$ have diagonal $(a,b,c,d,a,b)$ and only off-diagonal pairs $M_{01,10}=-a$, $M_{02,11}=-b$. Suppose $a>0$, $b>4$, $ac>b^2$, and $(b-4)(d-1)>(a+2)^2$. With $u=2|01\rangle+|10\rangle$, put $T=2a+2b+c+d-5$ and $\rho=(M-|u\rangle\langle u|)/T$. Then $T>0$, $\rho$ is a full-rank density operator, $M/T$ is separable, and $WM^\Gamma=0$. Moreover,
--   $$R_g(\rho)\le5/T,\qquad R_s(\rho)\ge16/(3T),\qquad R_s(\rho)-R_g(\rho)\ge1/(3T).$$
--   The parameters $(2,5,13,18)$ recover $\rho_*$ and $T=40$.
--
--   PDF p.26 following S148: retain the exact parameter specialization (2,5,13,18), T=40.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 26, IX.B — open parameter family of strict gaps

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 26, open parameter family of strict gaps.
Round-one coverage restoration: PDF p.26 following S148: retain the exact parameter specialization (2,5,13,18), T=40. -/
theorem parameterFamilyGap (a b c d : ℝ) (ha : 0<a) (hb : 4<b)
  (hac : b^2<a*c) (hbd : (a+2)^2<(b-4)*(d-1)) :
  0<familyT a b c d ∧ (familyM a b c d-proj noiseKet).PosDef ∧
  QAlgorithms.IsDensityMatrix (familyRho a b c d) ∧ (familyRho a b c d).PosDef ∧
  QAlgorithms.Entanglement.IsSeparablePositive (((familyT a b c d)⁻¹:ℂ) • familyM a b c d) ∧
  witnessW*pt (familyM a b c d)=0 ∧
  rg (familyRho a b c d)≤5/familyT a b c d ∧
  16/(3*familyT a b c d)≤rs (familyRho a b c d) ∧
  1/(3*familyT a b c d)≤rs (familyRho a b c d)-rg (familyRho a b c d) ∧
  familyRho 2 5 13 18 = rhoStar ∧ familyT 2 5 13 18 = 40 := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
