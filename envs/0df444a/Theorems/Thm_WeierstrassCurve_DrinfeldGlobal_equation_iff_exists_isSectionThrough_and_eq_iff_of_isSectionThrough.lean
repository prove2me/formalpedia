-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
-- name    : WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/3992ae11-db43-59a1-8677-e3436c693f68
-- title:
--   Sections of the finite chart versus affine Weierstrass points
-- statement:
--   Let $T$ be a commutative ring and let $W$ be a Weierstrass cubic over $T$ in projective form, with associated projective model $\mathrm{Proj}$ of the graded quotient `projModelGradingCR W` together with its structure morphism `projModelStrCR W` to $\mathrm{Spec}\,T$. A *section* of $W$ is a pair consisting of a morphism of schemes $\mathrm{Spec}\,T \to \mathrm{Proj}$ together with a proof that this morphism followed by `projModelStrCR W` is the identity of $\mathrm{Spec}\,T$. A section $S$ *passes through* $(x,y) \in T \times T$, written `IsSectionThrough S x y`, when there is a ring homomorphism $\chi$ from the degree-zero homogeneous localisation `ZChartRing W` of `projModelGradingCR W` at the class of the third coordinate to $T$ such that the underlying morphism of $S$ equals $\mathrm{Spec}(\chi)$ followed by the chart immersion `zChartι W`, and such that $\chi$ sends `xOverZ W` to $x$ and `yOverZ W` to $y$. The theorem asserts two things: first, for all $x, y \in T$, the pair $(x,y)$ satisfies the affine Weierstrass equation of `W.toAffine` if and only if some section of $W$ passes through $(x,y)$; second, for all sections $S, S'$ and all $x, y, x', y' \in T$ with $S$ passing through $(x,y)$ and $S'$ through $(x',y')$, one has $S = S'$ if and only if $x = x'$ and $y = y'$.
--
--   This is the dictionary between $T$-valued sections of the projective Weierstrass model that land in the chart where the third coordinate is invertible and solutions in $T$ of the affine Weierstrass equation; the second clause records both that the affine coordinates of such a section are well defined and that a section is determined by them. It is used throughout the treatment of level structures, where Drinfeld bases are formulated in terms of sections of the projective model while the computations are carried out with affine coordinates and division polynomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_PointChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) :
    (∀ x y : T, W.toAffine.Equation x y ↔ ∃ S : Section W, IsSectionThrough S x y) ∧
    (∀ (S S' : Section W) (x y x' y' : T), IsSectionThrough S x y → IsSectionThrough S' x' y' →
      (S = S' ↔ (x = x' ∧ y = y'))) := by sorry
