-- Prove2me | Theorems.Thm_UniqueFactorizationMonoid_exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity
-- name    : UniqueFactorizationMonoid.exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/c60d72ce-cdac-53d8-b797-71ce0cf9b564
-- title:
--   Kummer normal form for elements of a UFD
-- statement:
--   Let $R$ be a commutative ring that is a domain and a unique factorisation domain. Let $s \in R$ be a prime element, let $e$ be a natural number with $e > 0$, and let $f \in R$ be nonzero. Assume that for every prime element $p$ of $R$ that is not associated to $s$, the natural number $e$ divides `multiplicity p f`, the multiplicity of $p$ in $f$ (equivalently, the exponent of $p$ in the factorisation of $f$). The conclusion asserts the existence of a unit $w \in R^\times$, a natural number $k$, and an element $g \in R$ such that $$f = w \, s^{k} \, g^{e},$$ the equality being between $f$ and the product of the underlying element of $w$ with $s^k$ and $g^e$. No bound on $k$ is claimed, and $g$ is not asserted to be prime to $s$ or otherwise normalised.
--
--   This is the elementary divisor-theoretic step underlying the Kummer-theoretic part of Abhyankar's lemma: an element whose divisor is $e$-divisible away from one prime is, up to a unit and a power of that prime, an $e$-th power. It is used in the construction of an algebra isomorphism with $\mathrm{AdjoinRoot}$ of a polynomial $X^e - c$ over a regular local ring that is unramified outside a cyclic situation, in [`IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot`](thm.html#IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UniqueFactorizationMonoid_exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem UniqueFactorizationMonoid.exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (s : R) (hs : Prime s) (e : ℕ) (he : 0 < e) (f : R) (hf : f ≠ 0)
    (hdiv : ∀ p : R, Prime p → ¬ Associated p s → e ∣ multiplicity p f) :
    ∃ (w : Rˣ) (k : ℕ) (g : R), f = (w : R) * s ^ k * g ^ e := by sorry
