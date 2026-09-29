-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_moduleFinite_represents_isDrinfeldBasisOver_of_two_le
-- name    : WeierstrassProjModel.RelativeGroupLaw.exists_moduleFinite_represents_isDrinfeldBasisOver_of_two_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/40f36179-b740-5b6e-a429-c228d88d8f0a
-- title:
--   Module-finite representability of relative Drinfeld Γ(q)-bases
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$ whose associated affine curve is elliptic; write $\pi\colon \operatorname{Proj}(\text{projModelGradingCR } V)\to \operatorname{Spec} R$ for the structure morphism `projModelStrCR V`, and for a morphism $t\colon T\to\operatorname{Spec} R$ let a section over $t$ mean a morphism $T\to\operatorname{Proj}$ whose composite with $\pi$ is $t$. Let $G$ be a `RelativeGroupLaw`, i.e. a functorial group structure on the sets of sections over each $t$, with multiplication, unit and inversion satisfying associativity, the unit laws, left inverses, and compatibility with base change along any $\psi$ over $\operatorname{Spec} R$. Let $ev$ be, for every field $F$ with an $R$-algebra structure, a bijection between the sections over $\operatorname{Spec}(R\to F)$ and the points of the affine curve of $V\otimes_R F$, and let $hev$ assert `IsPointsEval`: $ev$ turns the group law $G$ into addition of points and intertwines the twist of a section by $\sigma\in\operatorname{Aut}_R(F)$ with the induced map on points. Finally let $q\in\mathbb{N}$ with $2\le q$. The conclusion: there exist a commutative ring $C$ that is an $R$-algebra and module-finite over $R$, and sections $P^{\mathrm u},Q^{\mathrm u}$ over $\operatorname{Spec}(R\to C)$ forming a Drinfeld $\Gamma(q)$-basis there, in the sense that the ideal sheaf data `basisDivisorOver` attached to the tuple $G.\text{basisTupleOver}\,q$ of combinations of $P^{\mathrm u},Q^{\mathrm u}$ equals the $q$-torsion ideal sheaf data `torsionIdealOver`, and such that for every $R$-algebra $T$ and every pair $P,Q$ of sections over $\operatorname{Spec}(R\to T)$ the pair $(P,Q)$ is a Drinfeld $\Gamma(q)$-basis in the same sense if and only if there is a unique $R$-algebra homomorphism $\psi\colon C\to T$ with $\operatorname{Spec}(\psi)$ followed by $P^{\mathrm u}$ equal to $P$ and $\operatorname{Spec}(\psi)$ followed by $Q^{\mathrm u}$ equal to $Q$. The universal property is thus tested only on affine $R$-schemes $\operatorname{Spec} T$ with $T$ in the same universe.
--
--   This is the representability of the moduli problem of Drinfeld $\Gamma(q)$-bases on the given elliptic Weierstrass model by a scheme affine and finite over the base, in the style of Katz–Mazur's treatment of Drinfeld level structures, here in the restricted form of a universal object among affine $R$-schemes. It is used by [`WeierstrassCurve.DrinfeldGlobal.exists_moduleFinite_represents_isLevel`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_moduleFinite_represents_isLevel), and its proof cites the finiteness and flatness of the $q$-torsion subscheme, the existence of an ideal sheaf cutting out the Drinfeld-basis locus, and the factorisation of a Drinfeld basis through the $q$-torsion scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_exists_moduleFinite_represents_isDrinfeldBasisOver_of_two_le.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.exists_moduleFinite_represents_isDrinfeldBasisOver_of_two_le
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) (q : ℕ) (hq : 2 ≤ q) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Module.Finite R C)
      (Pu Qu : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R C))) (projModelStrCR V))
      (_ : G.IsDrinfeldBasisOver q (Spec.map (CommRingCat.ofHom (algebraMap R C))) Pu Qu),
      ∀ (T : Type u) [CommRing T] [Algebra R T]
        (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) (projModelStrCR V)),
        G.IsDrinfeldBasisOver q (Spec.map (CommRingCat.ofHom (algebraMap R T))) P Q ↔
          ∃! ψ : C →ₐ[R] T,
            Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Pu.1 = P.1 ∧
            Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Qu.1 = Q.1 := by sorry
