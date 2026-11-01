-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P98_stinespring_spectralNorm_infimum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P98.stinespring_spectralNorm_infimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:55:55.801535+00:00
-- url     : https://prove2.me/theorems/2f40af94-7d8e-4ac3-8c83-a4d79c6a4ebd
-- title:
--   Diamond norm as an infimum over Stinespring pairs
-- statement:
--   Let $X=\mathbb C^n$ and $Y=\mathbb C^m$, $n,m\ge1$, and let $\Phi:L(X)\to L(Y)$ be any complex-linear map. For every finite positive-dimensional environment $Z$, consider all pairs $A,B:X\to Y\otimes Z$ satisfying $\Phi(T)=\operatorname{Tr}_Z(ATB^*)$ for every $T\in L(X)$. Then
--   $$
--   \|\Phi\|_\diamond=\inf_{Z,A,B}\|A\|_\infty\|B\|_\infty.
--   $$
--   The norms on $A,B$ are spectral norms. The infimum ranges over all such pairs, without a minimal-rank restriction and without claiming attainment. The zero map admits the zero pair in a one-dimensional environment.
--
--   This characterizes the completely bounded trace norm through dilation operators. Watrous gives a new SDP-duality proof of the result previously treated in KSV02 and Pau02.
-- source:
--   Semidefinite programs for completely bounded norms, arXiv:0901.4709v2, PDF p. 12, Theorem 5 (Stinespring spectral-norm characterization)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P98

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P98

/-- PDF pp.12--13, Theorem 5, reproved after KSV02 and Pau02:
a genuine infimum over every Stinespring pair, with no assertion of attainment. -/
theorem stinespring_spectralNorm_infimum {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    IsGLB (stinespringProducts Phi) (stabilizedTraceNorm Phi) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P98

end
