-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_isotropic_compatibility_region
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.isotropic_compatibility_region
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:28:51.582038+00:00
-- url     : https://prove2.me/theorems/f9505c69-e3e7-4696-b624-4438f8050d21
-- title:
--   Isotropic-state compatibility and the cloning region
-- statement:
--   Let $d\ge2$, $p,q\in\mathbb R$, and $|\Omega\rangle=d^{-1/2}\sum_a|a,a\rangle$. Define the normalized isotropic operators $\rho_p=p|\Omega\rangle\langle\Omega|+(1-p)I/d^2$ and $\rho_q$ in the fixed computational basis. There exists a positive trace-one joint state $\rho_{AB_1B_2}$ with marginals $\rho_{AB_1}=\rho_p$, $\rho_{AB_2}=\rho_q$ if and only if a CPTP $1\to2$ channel has marginal maps $D_p,D_q$. Equivalently, with $s=p+q$ and $t=p-q$,
--
--   $$
--   \exists\lambda\in[0,d],\quad
--   (d^2-1)t^2+(d^2-1)^2\left(s-\frac{\lambda d-2}{d^2-1}\right)^2\le\lambda^2.
--   $$
--
--   Both compatibility directions are included. The joint density is $C_T/d$, and the converse uses $C_T=d\rho$ because the reference marginal is $I/d$.
--
--   This transfers the region to state compatibility. The literal singlet overlap is $p+(1-p)/d^2$, not the shrink parameter $p$.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 1, Unnumbered main equivalence: two isotropic states sharing a subsystem

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.1–2,5,12: compatibility of two normalized isotropic states with shared A
is equivalent to cloning compatibility and hence to the full ellipse-union criterion.
The normalized state is C_T/d; its A marginal is I/d. -/
theorem isotropic_compatibility_region (d : ℕ) (hd : 2 ≤ d) (p q : ℝ) :
    (IsotropicCompatible d p q ↔ CloningAchievable d p q) ∧
    (IsotropicCompatible d p q ↔ InEllipseUnion d (p + q) (p - q)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
