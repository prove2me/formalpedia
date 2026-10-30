-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_general_cloning_ellipse_union
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.general_cloning_ellipse_union
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:22:48.829692+00:00
-- url     : https://prove2.me/theorems/02627804-5c53-4d2a-91b1-4cb443026c17
-- title:
--   Complete cloning region as a union of ellipses
-- statement:
--   Let $d\ge2$ and $p,q\in\mathbb R$. There exists a complex-linear CPTP map $T:M_d\to M_d\otimes M_d$ whose marginal maps are $D_p(X)=pX+(1-p)\operatorname{Tr}(X)I/d$ and $D_q$ if and only if, putting $s=p+q$, $t=p-q$, $a=(d^2-1)^{-1/2}$ and $b=(d^2-1)^{-1}$,
--
--   $$
--   \exists\lambda\in[0,d],\qquad
--   \frac{t^2}{a^2}+\frac{\left(s-\frac{\lambda d-2}{d^2-1}\right)^2}{b^2}\le\lambda^2.
--   $$
--
--   Both endpoints of the parameter interval are included; there are no extra assumptions on a six-operator coefficient representation.
--
--   The criterion gives necessity and attainability for the unrestricted physical region.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 12, Theorem 6: complete cloning region is a union of ellipses

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

/-- PDF p.12, Theorem 6, Eq.(10): the full admissible region is precisely the union;
no coefficient-wise PSD conditions or small-d multiplicities are assumed. -/
theorem general_cloning_ellipse_union (d : ℕ) (hd : 2 ≤ d) (p q : ℝ) :
    CloningAchievable d p q ↔ InEllipseUnion d (p + q) (p - q) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
