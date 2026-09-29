-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_algebraTower_of_mul_eq
-- name    : WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_algebraTower_of_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/c0622615-18b5-530a-be63-fe0ed3b7d874
-- title:
--   Agreement of relative group laws descends from K-points to F-points
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a separated morphism. Let $F$ be a field with an $R$-algebra structure, and $K$ a field carrying an $R$-algebra structure and an $F$-algebra structure such that the structure maps form a scalar tower, i.e. $R \to K$ is the composite $R \to F \to K$. Let $G_0$ and $G_1$ be two relative group laws on $f$, each consisting of multiplication, unit and inversion operations on the sets $\{\varphi \colon T \to A \mid \varphi \text{ followed by } f = t\}$ of $A$-valued points over an arbitrary $R$-scheme $(T,t)$, satisfying associativity, the two-sided unit law, left inversion, and compatibility with base change of the test scheme. Assume that for all $P, Q$ in the set of morphisms $\operatorname{Spec} K \to A$ lying over $\operatorname{Spec} R$ via the structure map of $K$, the multiplications of $G_0$ and of $G_1$ applied to $P,Q$ coincide. Then the same holds with $K$ replaced by $F$: the multiplications of $G_0$ and $G_1$ agree on every pair of points of $A$ over $\operatorname{Spec} F$.
--
--   A rigidity statement for relative group laws on a Weierstrass model: uniqueness of the group law verified on points over a large field descends to points over a subfield. It is used in the comparison of relative group laws via the zero section for elliptic models, [`WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso`](thm.html#WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_algebraTower_of_mul_eq.lean

import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_algebraTower_of_mul_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    [IsSeparated f]
    (F : Type u) [Field F] [Algebra R F]
    (K : Type u) [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
    (G₀ G₁ : WeierstrassProjModel.RelativeGroupLaw R f)
    (hK : ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
        G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q
          = G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q) :
    ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) f,
      G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q
        = G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q := by sorry
