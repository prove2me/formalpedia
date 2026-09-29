-- Prove2me | Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild
-- name    : ValuationSubring.exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/50b00b1a-06db-51c1-84c9-18b408d95c46
-- title:
--   Frobenius at a place of ℚ̄ and wild commutators with inertia
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb Q}$ lies in `A.nonunits`, and let $K$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ that is finite-dimensional over $\mathbb Q$. Then there exist an integer $d > 0$ and a $\mathbb Q$-algebra automorphism $\varphi$ of $\overline{\mathbb Q}$ such that: $\varphi z = z$ for all $z \in K$; $\varphi$ is a Frobenius element at $A$ for the exponent $p^d$, in the sense of `A.IsFrobeniusAt`, namely $\varphi$ belongs to the decomposition subgroup of $A$ over $\mathbb Q$ and the induced action on the residue field of $A$ is $x \mapsto x^{p^d}$; and, for every automorphism $\tau$ lying in `A.inertiaSubgroupIn ℚ` (the image in the full automorphism group of the inertia subgroup of $A$ over $\mathbb Q$), the element $w = \varphi\,\tau\,\varphi^{-1}\,(\tau^{p^d})^{-1}$ satisfies three conditions: $w$ again lies in `A.inertiaSubgroupIn ℚ`; for every $z \neq 0$ in $\overline{\mathbb Q}$ one has $w(z)z^{-1} - 1 \in$ `A.nonunits`; and for every intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ which is finite-dimensional and normal over $\mathbb Q$ there is $a \in \mathbb N$ with $w^{p^a}$ acting as the identity on $F$.
--
--   This packages the classical local structure at a finite place of residue characteristic $p$ — existence of a Frobenius lift fixing a given number field, the relation $\varphi \tau \varphi^{-1} \equiv \tau^{q}$ modulo wild inertia, and the fact that wild inertia is pro-$p$ — in terms of the absolute Galois group of $\mathbb Q$ and a valuation subring of $\overline{\mathbb Q}$. It is used in the local analysis of Galois actions on torsion of quaternionic objects, via [`QuaternionAlgebra.IsOrder.smul_eq_of_mem_inertiaSubgroupIn_of_mem_torsionBy_of_forall_isUnit_tensorProduct_padic`](thm.html#QuaternionAlgebra.IsOrder.smul_eq_of_mem_inertiaSubgroupIn_of_mem_torsionBy_of_forall_isUnit_tensorProduct_padic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] :
    ∃ (d : ℕ) (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), 0 < d ∧ (∀ z ∈ K, φ z = z) ∧
      A.IsFrobeniusAt φ (p ^ d) ∧
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ A.inertiaSubgroupIn ℚ →
        φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹ ∈ A.inertiaSubgroupIn ℚ ∧
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 →
          (φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹) z * z⁻¹ - 1 ∈ A.nonunits) ∧
        ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F],
          ∃ a : ℕ, ∀ x ∈ F, ((φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹) ^ (p ^ a)) x = x := by sorry
