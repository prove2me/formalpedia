-- Prove2me | Theorems.Thm_ValuationSubring_exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt
-- name    : ValuationSubring.exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/9f9ca4a5-f7f1-52ab-80f3-db92e30ec44b
-- title:
--   Quadratic Frobenius-parity character of a decomposition group at r
-- statement:
--   Let $r$ be a natural number which is prime, and let $A$ be a valuation subring of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ such that $A$ lies over $r$, meaning that the image of $r$ in $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ is a non-unit of $A$ (equivalently, $r$ lies in the maximal ideal of $A$). Write $D = A.\mathrm{decompositionSubgroup}\ \mathbb{Q}$ for the decomposition subgroup of $A$ inside $\mathrm{AlgebraicClosure}\ \mathbb{Q} \simeq_{\mathrm{alg}[\mathbb{Q}]} \mathrm{AlgebraicClosure}\ \mathbb{Q}$, acting on the residue field of $A$. The assertion is that there exists a monoid homomorphism $\chi : D \to \mathrm{Multiplicative}(\mathbb{Z}/2)$, that is a homomorphism to the two-element group written multiplicatively, with three properties. First, $\chi \tau = 1$ for every $\tau \in D$ whose underlying automorphism lies in `A.inertiaSubgroupIn ℚ`, the image in the full automorphism group of the inertia subgroup of $A$ under the inclusion of $D$. Second, $\chi \varphi \ne 1$ for every $\varphi \in D$ whose underlying automorphism $\sigma$ satisfies `A.IsFrobeniusAt σ r`, i.e. $\sigma$ lies in $D$ and acts on the residue field of $A$ by $x \mapsto x^{r}$. Third, for every $\sigma \in D$, $\chi \sigma = 1$ holds if and only if $\sigma \cdot x = x$ for all $x$ in the residue field of $A$ with $x^{r^{2}} = x$.
--
--   This is the unramified quadratic character of a decomposition group of $\overline{\mathbb{Q}}$ at $r$, recording the parity of the power of Frobenius by which an element acts on the residue field; the third clause, cutting out the subgroup fixing $\mathbb{F}_{r^{2}}$ pointwise, determines $\chi$ uniquely. It is used in the Čerednik–Drinfel'd descent statements [`CerednikDrinfeld.exists_descentIntertwiningBase_of_moduliTowerWitness_one_zero_of_two_mul_dvd`](thm.html#CerednikDrinfeld.exists_descentIntertwiningBase_of_moduliTowerWitness_one_zero_of_two_mul_dvd) and [`CerednikDrinfeld.exists_descentIntertwiningBase_of_moduliTowerWitness_zero_one_of_two_mul_dvd`](thm.html#CerednikDrinfeld.exists_descentIntertwiningBase_of_moduliTowerWitness_zero_one_of_two_mul_dvd), where a quadratic unramified twist at $r$ is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ χ : ↥(A.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2),
      (∀ τ : ↥(A.decompositionSubgroup ℚ),
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → χ τ = 1) ∧
      (∀ φ : ↥(A.decompositionSubgroup ℚ),
          A.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) r → χ φ ≠ 1) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
          χ σ = 1 ↔ ∀ x : ResidueField ↥A, x ^ (r ^ 2) = x → σ • x = x) := by sorry
