-- Prove2me | Theorems.Thm_TransportGlue_exists_pairing_of_linearEquiv
-- name    : TransportGlue.exists_pairing_of_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/057fe571-2a4a-5833-b917-77943e6f94db
-- title:
--   Transport of a perfect self-adjoint pairing along an equivariant isomorphism
-- statement:
--   Let $\mathcal O$, $A$, $A'$ be commutative rings with $A$ and $A'$ algebras over $\mathcal O$, and let $M$ be an $\mathcal O$-module that is also an $A$-module compatibly (scalar tower $\mathcal O \to A \to M$), and $N$ an $\mathcal O$-module that is also an $A'$-module compatibly. Suppose given an $\mathcal O$-linear isomorphism $s \colon M \to N$, a map $\varphi \colon A \to A'$ of underlying sets which is surjective, and the equivariance $s(a \cdot m) = \varphi(a) \cdot s(m)$ for all $a \in A$, $m \in M$. Suppose further given an $\mathcal O$-bilinear form $B \colon M \to M \to \mathcal O$ (an $\mathcal O$-linear map into $\mathcal O$-linear maps) that is self-adjoint for $A$, i.e. $B(a \cdot m, n) = B(m, a \cdot n)$ for all $a \in A$ and $m, n \in M$, and whose associated map $M \to \operatorname{Hom}_{\mathcal O}(M, \mathcal O)$ is bijective. The conclusion asserts the existence of an $\mathcal O$-bilinear form $B' \colon N \to N \to \mathcal O$ such that $B'(n, n') = B(s^{-1}n, s^{-1}n')$ for all $n, n' \in N$, such that $B'(a' \cdot n, n') = B'(n, a' \cdot n')$ for all $a' \in A'$ and $n, n' \in N$, and such that the induced map $N \to \operatorname{Hom}_{\mathcal O}(N, \mathcal O)$ is bijective. Note that $\varphi$ is only assumed to be a surjective function, not a ring homomorphism.
--
--   This is the transport of a perfect, Hecke-self-adjoint $\mathcal O$-bilinear pairing across an equivariant identification of modules, the algebra acting on the target being a quotient-like image of the algebra acting on the source. It is used in the construction of a perfect self-adjoint pairing on the cohomological carrier module attached to parabolic homomorphisms, where a pairing already available on one model must be moved along an equivariant isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TransportGlue_exists_pairing_of_linearEquiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TransportGlue.exists_pairing_of_linearEquiv
    {𝒪 A A' M N : Type} [CommRing 𝒪] [CommRing A] [CommRing A'] [Algebra 𝒪 A] [Algebra 𝒪 A']
    [AddCommGroup M] [Module 𝒪 M] [Module A M] [IsScalarTower 𝒪 A M]
    [AddCommGroup N] [Module 𝒪 N] [Module A' N] [IsScalarTower 𝒪 A' N]
    (s : M ≃ₗ[𝒪] N) (φ : A → A') (hφ : Function.Surjective φ) (hs : ∀ (a : A) (m : M), s (a • m) = φ a • s m)
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (a : A) (m n : M), B (a • m) n = B m (a • n)) (hBbij : Function.Bijective B) :
    ∃ B' : N →ₗ[𝒪] N →ₗ[𝒪] 𝒪, (∀ n n' : N, B' n n' = B (s.symm n) (s.symm n')) ∧
      (∀ (a' : A') (n n' : N), B' (a' • n) n' = B' n (a' • n')) ∧ Function.Bijective B' := by sorry
