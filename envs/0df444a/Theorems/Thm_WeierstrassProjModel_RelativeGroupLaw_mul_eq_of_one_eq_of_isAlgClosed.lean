-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isAlgClosed
-- name    : WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/ec932b35-b4c8-5141-aa4a-612e0dd73cf4
-- title:
--   Relative group laws with equal unit agree on K-points
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism, and let $K$ be an algebraically closed field which is an $R$-algebra; write $u : \operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism induced by the structure map $R \to K$. Assume that the second projection $A \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$ is proper, that the scheme $A \times_{\operatorname{Spec} R} \operatorname{Spec} K$ is integral, and that the fibre product of this projection with itself, i.e. $(A \times_{\operatorname{Spec} R} \operatorname{Spec} K) \times_{\operatorname{Spec} K} (A \times_{\operatorname{Spec} R} \operatorname{Spec} K)$, is reduced. Let $G_1, G_2$ be two terms of [`WeierstrassProjModel.RelativeGroupLaw R f`](def/WeierstrassCurve_ProjModel.html#L67), that is, two systems assigning to every scheme $T$ and every morphism $t : T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set of $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, subject to associativity, the two unit laws, left inverses, and naturality of multiplication under precomposition with morphisms $\psi : T' \to T$ over $\operatorname{Spec} R$. If the units of $G_1$ and $G_2$ at $t = u$ coincide, then for all $P, Q$ lying over $u$ the products $G_1.\mathrm{mul}_u(P,Q)$ and $G_2.\mathrm{mul}_u(P,Q)$ coincide.
--
--   This is the functor-of-points form, for the project's notion of relative group law on an $R$-scheme, of the rigidity consequence that a group law on a proper integral variety is determined by its identity element; here it is stated at the level of points over an algebraically closed $R$-field $K$. It is used in the comparison of group laws on Weierstrass projective models, feeding [`WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso`](thm.html#WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isAlgClosed.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
  GoodReductionJacobian WeierstrassProjModel

universe u

theorem WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isAlgClosed
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    [IsIntegral ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    [IsReduced ↑(pullback
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))]
    (G₁ G₂ : WeierstrassProjModel.RelativeGroupLaw R f)
    (h : G₁.one (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        = G₂.one (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
      G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q
        = G₂.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q := by sorry
