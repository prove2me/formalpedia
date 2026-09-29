-- Prove2me | Theorems.Thm_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime
-- name    : ValuationSubring.exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/bdf34f19-bd4d-5cb8-a1a9-d1f157b45623
-- title:
--   Frobenius conjugation raises tame inertia to the q-th power
-- statement:
--   Let $q$ be a prime number and let $A$ be a valuation subring of $\overline{\mathbb Q}$ (realised as `AlgebraicClosure ℚ`) satisfying the project's condition `A.LiesOverPrime q`, which unfolds to the statement that the image of $q$ in $\overline{\mathbb Q}$ lies in `A.nonunits`, the set of nonunits of $A$, i.e. its maximal ideal; so $A$ is a place above $q$. Write $I_A$ for `A.inertiaSubgroupIn ℚ`, the subgroup of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ obtained as the image of the inertia subgroup of $A$ over $\mathbb Q$ under the inclusion of the decomposition subgroup into the whole automorphism group. The theorem asserts the existence of a $\mathbb Q$-algebra automorphism $\varphi$ of $\overline{\mathbb Q}$ with the following property: for every $\tau \in I_A$, the commutator-type element $\omega = \varphi\tau\varphi^{-1}(\tau^{q})^{-1}$ again lies in $I_A$, and $\omega$ is wild at $A$ in the sense that for every $z \in \overline{\mathbb Q}$ with $z \neq 0$ one has $\omega(z)z^{-1} - 1 \in$ `A.nonunits`. No further property of $\varphi$ (such as being a Frobenius element) is asserted.
--
--   This is the classical statement that conjugation by a Frobenius element raises tame inertia to the $q$-th power, packaged so that the tame character of $\tau$ and of $\varphi\tau\varphi^{-1}$ differ by a $q$-th power up to a wild element. It is used to show that characters through which inertia at $q$ acts on a Galois-stable line satisfy $c = c^{q}$, hence are trivial for $q = 2$, and feeds into the inertia computations for the Galois representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) : ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ τ ∈ A.inertiaSubgroupIn ℚ, φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ A.inertiaSubgroupIn ℚ ∧ ∀ z : AlgebraicClosure ℚ, z ≠ 0 → (φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹ - 1 ∈ A.nonunits := by sorry
