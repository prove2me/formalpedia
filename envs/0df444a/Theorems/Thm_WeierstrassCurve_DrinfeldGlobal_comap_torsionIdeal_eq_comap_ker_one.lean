-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comap_torsionIdeal_eq_comap_ker_one
-- name    : WeierstrassCurve.DrinfeldGlobal.comap_torsionIdeal_eq_comap_ker_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/389bf09e-33f7-5c31-a8ce-3fb372ca5563
-- title:
--   Torsion ideal pulled back along a point equals [q]^* of the origin
-- statement:
--   Let $T$ be a commutative ring and $W$ a Weierstrass curve over $T$, with projective model $A := \mathrm{Proj}$ of the graded quotient ring `projModelGradingCR` attached to $W$ and structure morphism $f :=$ `projModelStrCR W` $: A \to \operatorname{Spec} T$. Let $G$ be a relative group law on $f$, i.e. multiplication, unit and inverse operations on the sets $\{\varphi : Y' \to A \mid \varphi \circ f = t\}$ of $t$-points, for all $t : Y' \to \operatorname{Spec} T$, satisfying associativity, the two unit laws, the left inverse law and naturality of multiplication under base change. Fix $q \in \mathbb{N}$, a scheme $Y$ and an arbitrary morphism $\gamma : Y \to A$ (no compatibility with $f$ is imposed). Write $O : \operatorname{Spec} T \to A$ for the underlying morphism of $G.one(\mathbf{1})$ and $[q] :=$ `G.schemeNsmul q` $: A \to A$ for the underlying morphism of the $q$-fold $G$-sum of the identity point of $A$. The $q$-torsion ideal sheaf data `torsionIdeal G q` on $\mathrm{pullback}\,(f, \mathbf{1})$ is the kernel of the first projection of the fibre product of $[q]$ with $O$, followed by the canonical morphism `toPullbackId` $: A \to \mathrm{pullback}\,(f,\mathbf{1})$. The assertion is that the comap of this ideal sheaf data along $\gamma$ followed by `toPullbackId` coincides with the comap along $\gamma$ followed by $[q]$ of the kernel ideal sheaf data of the origin $O$.
--
--   The statement identifies the scheme-theoretic $q$-torsion, viewed through the canonical identification of $A$ with the fibre product of $f$ with the identity of $\operatorname{Spec} T$, as the inverse image of the ideal of the origin under multiplication by $q$: a $Y$-point $\gamma$ is $q$-torsion precisely to the order measured by $[q]\circ\gamma$ meeting the zero section. It is used in the computation of the torsion ideal in terms of the $q$-division series on the origin chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_comap_torsionIdeal_eq_comap_ker_one.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.comap_torsionIdeal_eq_comap_ker_one
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ)
    {Y : Scheme.{u}} (γ : Y ⟶ projModelCR W) :
    (torsionIdeal G q).comap (γ ≫ toPullbackId) =
      (Scheme.Hom.ker (G.one (𝟙 _)).1).comap (γ ≫ G.schemeNsmul q) := by sorry
