-- Prove2me | Theorems.Thm_TWLoc_frobenius_conj_mul_pow_inv_wild
-- name    : TWLoc.frobenius_conj_mul_pow_inv_wild
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/32837623-4419-5ef1-936b-4e98eb16e33c
-- title:
--   Frobenius conjugation is q-th power on inertia, up to wild part
-- statement:
--   Fix a natural number $q$ and a valuation subring $P$ of $\overline{\mathbb{Q}}$ (realised as `AlgebraicClosure ℚ`). Let $\varphi$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ which is a Frobenius element at $P$ for $q$, that is: $\varphi$ lies in the decomposition subgroup of $P$ over $\mathbb{Q}$ and the induced action of $\varphi$ on the residue field of $P$ sends every $x$ to $x^{q}$. Let $\tau$ be an automorphism lying in `P.inertiaSubgroupIn ℚ`, the image in the full automorphism group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of the inertia subgroup of $P$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup. The conclusion is a conjunction about the commutator-type element $\sigma := \varphi \tau \varphi^{-1} (\tau^{q})^{-1}$: first, $\sigma$ again lies in `P.inertiaSubgroupIn ℚ`; second, $\sigma$ is wild at $P$ in the sense that for every $z \in \overline{\mathbb{Q}}$ with $z \neq 0$ the element $\sigma(z) z^{-1} - 1$ lies in `P.nonunits`, the set of elements of valuation $< 1$ attached to $P$, i.e. the maximal ideal of $P$. No primality assumption on $q$, and no assumption relating $q$ to the residue characteristic of $P$, is made.
--
--   This is the classical relation $\varphi \tau \varphi^{-1} = \tau^{q}$ on tame inertia, in the sharper form that the discrepancy between $\varphi \tau \varphi^{-1}$ and $\tau^{q}$ is an inertia element acting trivially on all ratios $\sigma(z)/z$ modulo the maximal ideal. It is used in the construction of Frobenius elements with prescribed behaviour on inertia and, through that, in the extraction of an inertia character from an adic Galois representation with cyclotomic determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TWLoc_frobenius_conj_mul_pow_inv_wild.lean

import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TWLoc.frobenius_conj_mul_pow_inv_wild {q : ℕ} (P : ValuationSubring (AlgebraicClosure ℚ))
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : P.IsFrobeniusAt φ q)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ P.inertiaSubgroupIn ℚ ∧
      ∀ z : AlgebraicClosure ℚ, z ≠ 0 → (φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹ - 1 ∈ P.nonunits := by sorry
