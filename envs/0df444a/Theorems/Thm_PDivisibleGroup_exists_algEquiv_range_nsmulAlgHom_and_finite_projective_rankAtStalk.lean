-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
-- name    : PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/a15288cb-3dc2-56f4-b42e-68c976a6f4d9
-- title:
--   Multiplication by p on a p-divisible group is an isogeny of degree p^h
-- statement:
--   Let $R$ be a commutative ring, let $p,h$ be natural numbers, let $G$ be a $p$-divisible group of height $h$ over $R$ in the sense of the structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199), so $G$ consists of commutative Hopf $R$-algebras $A_v=G.\mathrm{level}\ v$ that are cocommutative and finite free over $R$ of rank $p^{vh}$, together with surjective coalgebra-and-algebra maps $\mathrm{transition}\ v\colon A_{v+1}\to A_v$ whose kernel is the ideal $\mathrm{torsionIdeal}\ R\ A_{v+1}\ (p^v)$, the image of the augmentation ideal of $A_{v+1}$ under the $p^v$-th convolution power of the identity; and let $v$ be a natural number. Write $\Phi=$ `nsmulAlgHom R (G.level (v+1)) p`, the $p$-th convolution power of $\mathrm{id}_{A_{v+1}}$, an $R$-algebra endomorphism of $A_{v+1}$, and let $C=\Phi(A_{v+1})$ be its range, an $R$-subalgebra. The conclusion is the conjunction of: there is an isomorphism of $R$-algebras $e\colon A_v\to C$ such that $e(\mathrm{transition}\ v\ a)=\Phi(a)$ in $A_{v+1}$ for every $a\in A_{v+1}$; $A_{v+1}$ is a finite $C$-module; $A_{v+1}$ is a projective $C$-module; there is a $C$-linear map $r\colon A_{v+1}\to C$ with $r(c)=c$ for all $c\in C$, i.e. a retraction of the inclusion; and $\mathrm{rankAtStalk}_C(A_{v+1})(\mathfrak q)=p^h$ for every prime $\mathfrak q$ of $C$.
--
--   This is the assertion, implicit in Tate's definition of a $p$-divisible group, that multiplication by $p$ factors as a finite locally free map $G_{v+1}\to G_v$ of constant degree $p^h$, identifying $G_v$ with the quotient of $G_{v+1}$ by its $p$-torsion at the level of coordinate rings. It is obtained from the general results on surjections of finite free Hopf algebras ([`HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective`](thm.html#HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective), [`HopfAlgebra.finite_projective_hopfKer_of_surjective`](thm.html#HopfAlgebra.finite_projective_hopfKer_of_surjective), [`HopfAlgebra.isHopfGalois_of_surjective`](thm.html#HopfAlgebra.isHopfGalois_of_surjective)), and is used in the construction of the comparison of levels and in the extraction of $p$-th roots of points on $p$-divisible groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) (v : ℕ) :
    (∃ e : G.level v ≃ₐ[R] ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p).range,
        ∀ a : G.level (v + 1),
          ((e (G.transition v a) : ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p).range) :
              G.level (v + 1)) =
            PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p a) ∧
      Module.Finite ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p).range (G.level (v + 1)) ∧
      Module.Projective ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p).range (G.level (v + 1)) ∧
      (∃ r : G.level (v + 1) →ₗ[↥(PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p).range]
          ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p).range,
        ∀ c : ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p).range,
          r (c : G.level (v + 1)) = c) ∧
      ∀ 𝔮 : PrimeSpectrum ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p).range,
        Module.rankAtStalk (R := ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (v + 1)) p).range)
          (G.level (v + 1)) 𝔮 = p ^ h := by sorry
