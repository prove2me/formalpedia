-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_projective_qubit_quotient_dichotomy
-- name    : QAlgorithms.Papers.Independent.Information100.P38.projective_qubit_quotient_dichotomy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:04:46.936469+00:00
-- url     : https://prove2.me/theorems/d277b5a2-573e-41dd-bf5d-8f26d57629e3
-- title:
--   Remark 1 and preceding dichotomy
-- statement:
--   Let $H=E|1\rangle\langle1|$ with $E>0$, and let $M_\pm=(I\pm\mathbf m\cdot\boldsymbol\sigma)/2$ with $|\mathbf m|=1$. Define the extended-real quotient using only density matrices with strictly positive incoherent ergotropy. Then
--
--   $$\sup_{\rho:E_{\rm inc}(\rho)>0}\frac{E_O(\rho,M)}{E_{\rm inc}(\rho)}=\begin{cases}1,&M\text{ incoherent},\\+\infty,&M\text{ coherent}.\end{cases}$$
--
--   For $\rho=(I+\mathbf v\cdot\boldsymbol\sigma)/2$, $|\mathbf v|\le1$, $v_z<0$, the pointwise ratio is $\tfrac12(1-|\mathbf v\cdot\mathbf m|/v_z)$. Negative ratios are allowed in the optimization; no value is assigned at a zero denominator. The dichotomy shows why this quotient cannot quantify the amount of advantage.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 4, Remark 1 and preceding dichotomy

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.4, Remark 1 and its preceding qubit dichotomy: quotient one for incoherent
projective measurements and positive infinity for every coherent projective measurement. -/
theorem projective_qubit_quotient_dichotomy (E : ℝ) (hE : 0 < E)
    (m : Fin 3 → ℝ) (hm : ergotropicBlochLengthSquared m = 1) :
    (measurementIncoherent (ergotropicBlochMeasurement m) →
      ergotropicQuotient E (ergotropicBlochMeasurement m) = 1) ∧
    (¬ measurementIncoherent (ergotropicBlochMeasurement m) →
      ergotropicQuotient E (ergotropicBlochMeasurement m) = ⊤) ∧
    (∀ v : Fin 3 → ℝ, ergotropicBlochLengthSquared v ≤ 1 → v 2 < 0 →
      observationalErgotropy ![0, E] (ergotropicBlochMeasurement m) (ergotropicBlochMatrix v) /
        incoherentErgotropy ![0, E] (ergotropicBlochMatrix v) =
          (1 / 2 : ℝ) * (1 - |ergotropicBlochDot v m| / v 2)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
