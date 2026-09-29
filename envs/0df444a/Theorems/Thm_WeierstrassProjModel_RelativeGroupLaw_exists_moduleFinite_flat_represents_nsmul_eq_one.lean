-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_moduleFinite_flat_represents_nsmul_eq_one
-- name    : WeierstrassProjModel.RelativeGroupLaw.exists_moduleFinite_flat_represents_nsmul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/2b265a10-3b31-5b0a-989e-41ebc671e641
-- title:
--   Representability of q-torsion by a module-finite flat algebra
-- statement:
--   Let $R$ be a commutative ring, let $V$ be a projective Weierstrass curve over $R$ whose associated affine curve is elliptic, and write $\mathtt{projModelStrCR}\,V$ for the structure morphism from $\mathrm{Proj}$ of the graded quotient ring of the projective model to $\operatorname{Spec} R$. Let $G$ be a relative group law on this model, i.e. an assignment, for every $R$-scheme $t : T \to \operatorname{Spec} R$, of a multiplication, an identity and an inversion on the set of sections $\{\varphi : T \to \mathrm{Proj} \mid \varphi \text{ followed by the structure morphism equals } t\}$, satisfying associativity, the two unit laws, left inverses, and compatibility with pullback along morphisms $\psi : T' \to T$ over $\operatorname{Spec} R$. Let $ev$ be a family of bijections, one for each field $F$ that is an $R$-algebra, between the sections over $\operatorname{Spec} F$ and the group of points of the affine curve $V.\mathtt{baseChange}\,F$, and let $hev$ assert that $ev$ is a homomorphism for $G$'s multiplication and commutes with the action of $R$-algebra automorphisms $\sigma$ of $F$ (twisting a section by $\operatorname{Spec}\sigma$ corresponds to transport of points along $\sigma$). Let $q$ be a positive natural number. The conclusion produces a commutative ring $C$ in the same universe, an $R$-algebra structure on $C$ making $C$ finite and flat as an $R$-module, and a section $Q_u$ over $\operatorname{Spec} C$ with $q \cdot Q_u = 1$, where $n \cdot x$ is the $n$-fold $G$-multiple of $x$ starting from the identity, such that for every $R$-algebra $T$ and every section $Q$ over $\operatorname{Spec} T$ one has $q \cdot Q = 1$ if and only if there is a unique $R$-algebra homomorphism $\psi : C \to T$ with $\operatorname{Spec}\psi$ followed by $Q_u$ equal to $Q$.
--
--   This is the representability of the $q$-torsion subscheme $E[q]$ of an elliptic curve over a base ring: it is affine, $\operatorname{Spec} C$ with $C$ module-finite and flat over $R$, and carries a universal $q$-torsion point. It rests on the finiteness, flatness and local finite presentation of the kernel scheme of $[q]$, and is used in the construction of the moduli rings and torsion-lifting discs for modular curves with level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_exists_moduleFinite_flat_represents_nsmul_eq_one.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.exists_moduleFinite_flat_represents_nsmul_eq_one
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) (q : ℕ) (hq : 0 < q) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Module.Finite R C) (_ : Module.Flat R C)
      (Qu : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R C))) (projModelStrCR V))
      (_ : G.nsmul _ q Qu = G.one _),
      ∀ (T : Type u) [CommRing T] [Algebra R T]
        (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) (projModelStrCR V)),
        G.nsmul _ q Q = G.one _ ↔
          ∃! ψ : C →ₐ[R] T, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Qu.1 = Q.1 := by sorry
