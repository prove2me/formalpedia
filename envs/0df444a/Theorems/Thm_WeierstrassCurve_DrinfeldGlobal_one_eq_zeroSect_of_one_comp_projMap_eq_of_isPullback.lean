-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
-- name    : WeierstrassCurve.DrinfeldGlobal.one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/8810f60a-734f-57ee-9519-45734f36661d
-- title:
--   Unit section equals zero section after base change
-- statement:
--   Let $T,T'$ be commutative rings (in a fixed universe), let $W$ be a projective Weierstrass curve over $T$, let $f\colon T\to T'$ be a ring homomorphism, and let $\varphi$ be a graded ring homomorphism from the graded ring $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,3)\,T/(W.\mathrm{polynomial})$, graded by the images of the homogeneous submodules, to the corresponding graded quotient for the base-changed curve $W.\mathrm{map}\,f$. Assume: the irrelevant ideal of the target is contained in the $\varphi$-image of the irrelevant ideal of the source (so that $\mathrm{Proj.map}\,\varphi$ exists); `IsCoefficientHom W f φ`, i.e. $\varphi$ carries the class of a constant $C\,a$ to the class of $C\,(f a)$ and the class of each coordinate $X_i$ ($i\in\mathrm{Fin}\,3$) to the class of $X_i$; and the square formed by $\mathrm{Proj.map}\,\varphi$, the structure morphisms $\mathrm{projModelStrCR}$ of the two Proj models and $\mathrm{Spec}\,f$ is cartesian. Let $G$, $G'$ be relative group laws (functorial group structures on $S$-points, with naturality of multiplication) on the structure morphisms over $T$ and over $T'$ respectively. Assume that for every scheme $S$ and every $s\colon S\to\operatorname{Spec} T$ the unit $G.\mathrm{one}\,s$ is $s$ followed by the zero section `kwZeroSect` of $W$, and that for every $s\colon S\to\operatorname{Spec} T'$ the unit $G'.\mathrm{one}\,s$ followed by $\mathrm{Proj.map}\,\varphi$ equals the unit $G.\mathrm{one}\,(s\circ \mathrm{Spec}\,f)$. Then for every scheme $S$ and every $s\colon S\to\operatorname{Spec} T'$ the unit $G'.\mathrm{one}\,s$ is $s$ followed by the zero section `kwZeroSect` of $W.\mathrm{map}\,f$.
--
--   This is the rigidity-free step identifying the neutral element of a transported group law with the point at infinity on the base-changed Weierstrass model: a group law on the Proj model over $T'$ obtained by descent along a cartesian square has its unit given by the canonical zero section. It is used in constructing group laws on Weierstrass models over arbitrary bases by transport from the universal curve, and is cited in the treatment of the origin chart, the $n$-fold multiplication morphisms and the evaluation of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (hP : IsPullback (Proj.map φ hφ) (projModelStrCR (W.map f)) (projModelStrCR W)
      (Spec.map (CommRingCat.ofHom f)))
    (G : RelativeGroupLaw T (projModelStrCR W)) (G' : RelativeGroupLaw T' (projModelStrCR (W.map f)))
    (hG : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T)), (G.one s).1 = s ≫ (kwZeroSect T W.toAffine).1)
    (hone : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T')),
      (G'.one s).1 ≫ Proj.map φ hφ = (G.one (s ≫ Spec.map (CommRingCat.ofHom f))).1)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T')) :
    (G'.one s).1 = s ≫ (kwZeroSect T' (W.map f).toAffine).1 := by sorry
