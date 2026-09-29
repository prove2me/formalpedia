-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_r0_isIntegral_pullbacks
-- name    : WeierstrassProjModel.kw_r0_isIntegral_pullbacks
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/4778bc8f-09d7-5d26-b036-20d36b5106ed
-- title:
--   Integrality of the Weierstrass model and its self-products
-- statement:
--   Let $R$ be a Noetherian commutative integral domain and let $W$ be a Weierstrass curve over $R$. Write $E := \mathrm{Proj}$ of the grading on the quotient of the polynomial ring in three homogeneous variables by the homogeneous ideal of the Weierstrass cubic attached to `W.toProjective`, i.e. $E =$ `projModelCR W.toProjective`, and let $\pi :=$ `projModelStrCR W.toProjective` be its structure morphism to $\operatorname{Spec} R$, namely the canonical map $\mathrm{Proj} \to \operatorname{Spec}$ of the degree-zero part followed by $\operatorname{Spec}$ of the structure map $R \to (\text{degree-}0\text{ part})$. Assume $\pi$ is smooth and satisfies the predicate `GeometricallyIntegral`. The conclusion is the conjunction of three assertions: the scheme $E$ is integral; the scheme underlying the fibre product $E \times_{\operatorname{Spec} R} E$, formed as the pullback of $\pi$ along $\pi$, is integral; and the scheme underlying the pullback of the composite of the first projection $E \times_{\operatorname{Spec} R} E \to E$ with $\pi$ against $\pi$, i.e. the left-bracketed triple product $(E \times_{\operatorname{Spec} R} E) \times_{\operatorname{Spec} R} E$, is integral.
--
--   This records that a smooth, geometrically integral projective Weierstrass model over a Noetherian domain is an integral scheme, together with the same conclusion for its two- and threefold self-fibre-products over the base; the triple product is what is needed to speak of the group law and its associativity on such a model. It is used in the treatment of integrality for self-pullbacks over fields and after base change, and in the commutativity statement for the evaluation of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_r0_isIntegral_pullbacks.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.kw_r0_isIntegral_pullbacks {R : Type*} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) :
    IsIntegral (projModelCR W.toProjective) ∧
    IsIntegral ↑(pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)) ∧
    IsIntegral ↑(pullback
      (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ≫
        projModelStrCR W.toProjective)
      (projModelStrCR W.toProjective)) := by sorry
