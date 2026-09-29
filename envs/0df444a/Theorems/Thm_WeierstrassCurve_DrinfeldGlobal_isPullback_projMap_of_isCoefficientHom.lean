-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
-- name    : WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/c89ae5cb-9619-5963-9141-db39d48f73df
-- title:
--   Proj of a Weierstrass model is cartesian over Spec f
-- statement:
--   Let $T$ and $T'$ be commutative rings in a fixed universe, let $W$ be a projective Weierstrass curve over $T$, and let $f : T \to T'$ be a ring homomorphism, so that $W.\mathrm{map}\,f$ is the projective Weierstrass curve over $T'$ obtained by applying $f$ to the coefficients. For a projective Weierstrass curve $V$ over a ring $R$, `projModelGradingCR V` denotes the natural $\mathbb{N}$-grading on the quotient $\mathrm{MvPolynomial}\,(\mathrm{Fin}\ 3)\ R / (V.\mathrm{polynomial})$, its degree-$i$ piece being the image of the homogeneous degree-$i$ submodule under the quotient map, and `projModelStrCR V` is the structure morphism $\mathrm{Proj}(\text{this grading}) \to \operatorname{Spec} R$ given by `Proj.toSpecZero` followed by $\operatorname{Spec}$ of the algebra map $R \to (\text{degree-}0\text{ piece})$. Let $\varphi$ be a graded ring homomorphism from `projModelGradingCR W` to `projModelGradingCR (W.map f)` such that the irrelevant ideal of the target is contained in the image under $\varphi$ of the irrelevant ideal of the source (the hypothesis $h\varphi$ making `Proj.map φ hφ` defined), and assume `IsCoefficientHom W f φ`, i.e. $\varphi$ sends the class of a constant $C\,a$ to the class of $C\,(f a)$ for every $a \in T$ and the class of each variable $X_i$, $i \in \mathrm{Fin}\ 3$, to the class of $X_i$. Then the square whose first projection is `Proj.map φ hφ` from $\mathrm{Proj}$ of the grading of $W.\mathrm{map}\,f$ to $\mathrm{Proj}$ of the grading of $W$, whose second projection is `projModelStrCR (W.map f)` to $\operatorname{Spec} T'$, and whose remaining sides are `projModelStrCR W` and $\operatorname{Spec}$ of $f$, commutes and is a pullback square.
--
--   This is the statement that the projective Weierstrass model commutes with base change of coefficients, in the pinned form: any graded homomorphism agreeing with $f$ on constants and fixing the three coordinate variables induces the canonical cartesian square, so the base-change isomorphism is identified with `Proj.map φ hφ` itself. It is used throughout the construction and representability arguments for Weierstrass-model moduli and Drinfeld level structures, where charts and level data must be transported along ring homomorphisms compatibly with the projective model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ) :
    IsPullback (Proj.map φ hφ) (projModelStrCR (W.map f)) (projModelStrCR W)
      (Spec.map (CommRingCat.ofHom f)) := by sorry
