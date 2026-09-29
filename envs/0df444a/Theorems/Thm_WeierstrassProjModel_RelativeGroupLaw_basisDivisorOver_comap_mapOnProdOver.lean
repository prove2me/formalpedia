-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_basisDivisorOver_comap_mapOnProdOver
-- name    : WeierstrassProjModel.RelativeGroupLaw.basisDivisorOver_comap_mapOnProdOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/43f1fd69-377b-529d-9dd9-e2d876318429
-- title:
--   Base change of the relative Drinfeld basis divisor and torsion ideal
-- statement:
--   Let $R$ be a commutative ring and $V$ a projective Weierstrass curve over $R$, and write $f =$ `projModelStrCR V` for the structure morphism $\operatorname{Proj}$ of the graded quotient ring of $V$ to $\operatorname{Spec} R$. Let $G$ be a `RelativeGroupLaw` for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to \operatorname{Proj} \mid \varphi \circ f = t\}$ of relative points, for all $t : T \to \operatorname{Spec} R$, with multiplication, unit, inverse, the group axioms and naturality in $T$. Fix $q \in \mathbb{N}$, schemes $T, T'$ with morphisms $t : T \to \operatorname{Spec} R$, $t' : T' \to \operatorname{Spec} R$, a morphism $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$, and two relative points $P, Q$ over $t$. Let $\mathrm{id} \times \psi$ denote `mapOnProdOver`, the induced morphism $\operatorname{Proj} \times_{\operatorname{Spec} R} T' \to \operatorname{Proj} \times_{\operatorname{Spec} R} T$. The assertion is a conjunction of two equalities of ideal sheaf data on $\operatorname{Proj} \times_{\operatorname{Spec} R} T'$. First, the comap along $\mathrm{id} \times \psi$ of `G.basisDivisorOver q t P Q`, the product over $i \in \mathrm{Fin}(q \cdot q)$ of the kernel ideal sheaves of the graphs of the relative points `G.linCombOver t P Q (i / q) (i % q)`, equals `G.basisDivisorOver q t' _ _` formed from the composites $\psi$ followed by $P$ and by $Q$. Second, the comap along $\mathrm{id} \times \psi$ of `G.torsionIdealOver q t` — the comap along the first projection of the kernel ideal sheaf of the first projection of the pullback of `G.schemeNsmul q` against the unit section over the identity of $\operatorname{Spec} R$ — equals `G.torsionIdealOver q t'`.
--
--   This is the base-change compatibility of the relative Drinfeld-basis data: the $q \times q$ divisor cut out by the linear combinations of a pair of relative points, and the $q$-torsion ideal, both commute with pullback along a morphism of test schemes over $\operatorname{Spec} R$. It underlies the representability statements for Drinfeld level structures on the Weierstrass model, and is cited in the characterisation of Drinfeld bases by vanishing of such ideal sheaf data and in the verification that level structures transport along morphisms over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_basisDivisorOver_comap_mapOnProdOver.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.basisDivisorOver_comap_mapOnProdOver
    {R : Type u} [CommRing R] {V : WeierstrassCurve.Projective R}
    (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P Q : SchemeHomOver t (projModelStrCR V)) :
    (G.basisDivisorOver q t P Q).comap (mapOnProdOver (projModelStrCR V) ψ hψ) =
        G.basisDivisorOver q t' (schemeHomOverComp ψ hψ P) (schemeHomOverComp ψ hψ Q) ∧
      (G.torsionIdealOver q t).comap (mapOnProdOver (projModelStrCR V) ψ hψ) = G.torsionIdealOver q t' := by sorry
