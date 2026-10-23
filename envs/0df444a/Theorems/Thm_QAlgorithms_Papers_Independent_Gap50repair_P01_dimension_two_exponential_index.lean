-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_dimension_two_exponential_index
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.dimension_two_exponential_index
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:24:36.365855+00:00
-- url     : https://prove2.me/theorems/12541c2e-d395-4e40-8eb6-0f49a9e7d0d7
-- title:
--   Proposition 41
-- statement:
--   Let $S$ be a real symmetric nonsingular $2\times2$ matrix, let $T>0$, and assume $e^{TJ_0S}\ne I$. Write $\sigma=\operatorname{Sign}S$, and let $a_1,a_2$ be its eigenvalues, so $a_1a_2=\det S$. For $\gamma(t)=e^{tJ_0S}$ on $[0,T]$,
--
--   $$\mu_{\rm CZ}(\gamma)=\begin{cases}\bigl(\tfrac12+\lfloor\sqrt{a_1a_2}\,T/(2\pi)\rfloor\bigr)\sigma,&\sigma\ne0,\\0,&\sigma=0.\end{cases}$$
--
--   The square root is used only in the definite branch. The floor argument follows the period calculation on p.44: duration multiplies the square root, rather than lying under it in a reading of the printed (46). This computes both orientations of rotation and the indefinite case.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 43, Proposition 41

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Proposition 41, PDF pp.43–44. Printed (46) has sqrt(a1*a2*T); change only
its floor argument to sqrt(a1*a2)*T, as required by the p.44 period
2*pi/sqrt(a1*a2) and concluding formula. Use det S=a1*a2; both definite
signs and the indefinite case are retained. S=I, T=3*pi gives index 3. -/
theorem dimension_two_exponential_index (S : GroupedRealMatrix 1) (hs : S.transpose = S)
    (hnd : S.det ≠ 0) (T : ℝ) (hT : 0 < T) (hend : exponentialPath S T ≠ 1) :
    conleyZehnder (exponentialPath S) T = if matrixSignature S = 0 then 0 else
      (2*Int.floor (Real.sqrt S.det*T/(2*Real.pi))+1)*(matrixSignature S/2) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
