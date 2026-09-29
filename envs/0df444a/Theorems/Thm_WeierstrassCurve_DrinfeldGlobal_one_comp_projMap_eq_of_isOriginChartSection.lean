-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection
-- name    : WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/15579744-8b9c-5bcd-b82a-82afc27611e5
-- title:
--   Unit sections are compatible with Proj base change
-- statement:
--   Let $T$ and $T'$ be commutative rings (in a fixed universe), let $W$ be a projective Weierstrass curve over $T$, and let $f : T \to T'$ be a ring homomorphism, so that $W.\mathrm{map}\,f$ is a projective Weierstrass curve over $T'$. Let $\varphi$ be a graded ring homomorphism from the graded quotient ring `projModelGradingCR W` (the quotient of the polynomial ring in three variables by the span of the Weierstrass cubic, graded by the images of the homogeneous submodules) to `projModelGradingCR (W.map f)`, subject to two hypotheses: the irrelevant ideal of the target is contained in the image under $\varphi$ of the irrelevant ideal of the source (so that `Proj.map φ hφ` is defined), and $\varphi$ is a coefficient homomorphism, meaning it sends the class of a constant $a \in T$ to the class of the constant $f(a)$ and fixes the class of each coordinate $X_i$, $i \in \mathrm{Fin}\,3$. Let $G$ be a relative group law on the structure morphism $\mathrm{Proj}(\mathtt{projModelGradingCR}\,W) \to \operatorname{Spec} T$ and $L$ one on the corresponding morphism for $W.\mathrm{map}\,f$ over $T'$; thus each assigns functorially, to every morphism $t$ to the base, a group structure on the sections over $t$, with unit, multiplication, inverse, the group axioms and naturality in $t$. Assume the unit section of $G$ at the identity of $\operatorname{Spec} T$ factors through the chart where the middle coordinate is invertible, via a ring homomorphism $\chi$ from the degree-zero homogeneous localisation `OriginChartRing W` to $T$ (that is, the underlying morphism of that unit section is $\operatorname{Spec}(\chi)$ followed by the chart immersion), and that $\chi$ kills both $x/y$ and $z/y$; assume the same for the unit section of $L$ with a homomorphism $\chi'$ into $T'$ killing $x/y$ and $z/y$ for $W.\mathrm{map}\,f$. The conclusion is the commutativity of the square: the underlying morphism of the unit section of $L$ followed by `Proj.map φ hφ` equals $\operatorname{Spec}(f)$ followed by the underlying morphism of the unit section of $G$.
--
--   This records that the identity sections of the two relative group laws are both the origin $(0:1:0)$ in the chart $y \neq 0$, and hence are matched by the morphism of $\mathrm{Proj}$'s induced by a coefficient homomorphism over $f$. It is the base-change compatibility of the zero section used in the representability arguments for Drinfeld level structures on families of Weierstrass curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (G : RelativeGroupLaw T (projModelStrCR W)) (L : RelativeGroupLaw T' (projModelStrCR (W.map f)))
    (χ : OriginChartRing W →+* T) (hχ : IsOriginChartSection (G.one (𝟙 _)) χ)
    (hχx : χ (xOverY W) = 0) (hχz : χ (zOverY W) = 0)
    (χ' : OriginChartRing (W.map f) →+* T') (hχ' : IsOriginChartSection (L.one (𝟙 _)) χ')
    (hχ'x : χ' (xOverY (W.map f)) = 0) (hχ'z : χ' (zOverY (W.map f)) = 0) :
    (L.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of T)))).1 := by sorry
