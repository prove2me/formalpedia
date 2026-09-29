-- Prove2me | Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild
-- name    : ValuationSubring.apply_eq_self_of_pow_apply_eq_self_of_wild
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/5c4ad2f7-db27-5af5-b235-3a81b639618c
-- title:
--   Wild automorphisms fix points fixed by prime-to-q powers
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $A$ be a valuation subring of $L$, with associated valuation $v =$ `A.valuation`. Let $q$ be a natural number whose image in $L$ lies in `A.nonunits`, i.e. $v(q) < 1$; so $A$ lies over $q$ in the sense that $q$ is a non-unit of $A$ (no primality of $q$ is assumed). Let $\sigma$ be a $K$-algebra automorphism of $L$ which is wild at $A$ in the elementwise sense that for every $z \in L$ with $z \neq 0$ the element $\sigma(z) z^{-1} - 1$ lies in `A.nonunits`, equivalently $v(\sigma z - z) < v(z)$. Let $m$ be a natural number coprime to $q$, and let $y \in L$ satisfy $\sigma^m(y) = y$. Then $\sigma(y) = y$.
--
--   This is an elementwise form of the statement that wild inertia at a place above $q$ is a pro-$q$ group: a wildly ramified automorphism has no nontrivial action of order prime to $q$, and the conclusion needs no ramification filtration, only the valuation inequality. It feeds the construction of simultaneous fixed vectors for prime-to-$q$ powers of wild automorphisms, being cited by [`ValuationSubring.exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal`](thm.html#ValuationSubring.exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal) and [`ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild`](thm.html#ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem ValuationSubring.apply_eq_self_of_pow_apply_eq_self_of_wild {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {q : ℕ} (hA : ((q : ℕ) : L) ∈ A.nonunits) {σ : L ≃ₐ[K] L}
    (hwild : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits) {m : ℕ} (hm : m.Coprime q) {y : L}
    (h : (σ ^ m) y = y) : σ y = y := by sorry
