-- Prove2me | Theorems.Thm_ValuationSubring_forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot
-- name    : ValuationSubring.forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/1374c2b8-1065-507d-a0b8-f907f7dba92a
-- title:
--   Transfer of genericity along monic relations between J and J'
-- statement:
--   Let $A$ be a commutative local ring, $K'$ a field carrying an $A$-algebra structure, and $V \subseteq K'$ a valuation subring. Assume that the structure map $A \to K'$ sends every element of $A$ into $V$, and sends every element of the maximal ideal of $A$ into `V.nonunits`, the set of elements of $K'$ of valuation less than $1$ (the maximal ideal of $V$). Let $J, J' \in K'$, and let $\Phi, \Psi \in \mathbb{Z}[X][Y]$ be monic in $Y$, such that $J'$ is a root of the polynomial in $K'[Y]$ obtained from $\Phi$ by evaluating each coefficient at $J$, and $J$ is a root of the polynomial obtained from $\Psi$ by evaluating each coefficient at $J'$. Suppose finally that for every $P \in A[X]$ whose reduction modulo the maximal ideal of $A$ is nonzero, both $P(J)$ and $P(J)^{-1}$ lie in $V$. The conclusion is the same assertion for $J'$: for every such $P$, both $P(J')$ and $P(J')^{-1}$ lie in $V$.
--
--   This is the transfer of the genericity of $J$ over the residue field of $A$ to any $J'$ tied to $J$ by a pair of monic integral relations, as furnished classically by the modular equation relating $j(\tau)$ and $j(N\tau)$. It is used in the analysis of membership in the Igusa–Gauss ring for $q$-expansions of functions on modular curves of full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot
    (A : Type*) [CommRing A] [IsLocalRing A] (K' : Type*) [Field K'] [Algebra A K']
    (V : ValuationSubring K')
    (hA : ∀ a : A, algebraMap A K' a ∈ V) (hAm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A K' a ∈ V.nonunits)
    (J J' : K')
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic)
    (hΦJ : (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K') J)).IsRoot J')
    (Ψ : Polynomial (Polynomial ℤ)) (hΨ : Ψ.Monic)
    (hΨJ : (Ψ.map (Polynomial.eval₂RingHom (Int.castRingHom K') J')).IsRoot J)
    (hgen : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval J P ∈ V ∧ (Polynomial.aeval J P)⁻¹ ∈ V) :
    ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval J' P ∈ V ∧ (Polynomial.aeval J' P)⁻¹ ∈ V := by sorry
