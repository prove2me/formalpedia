-- Prove2me | Theorems.Thm_Polynomial_dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero
-- name    : Polynomial.dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/5a147aba-edf2-528e-b921-ca061907a820
-- title:
--   Monic polynomial with separated roots divides any common vanishing polynomial
-- statement:
--   Let $T$ and $S$ be commutative rings and $f : T \to S$ an injective ring homomorphism. Let $\iota$ be a finite type, let $h \in T[X]$ be monic, and let $r : \iota \to S$ be a family of elements of $S$ such that the image $f_*h \in S[X]$ factors as $\prod_{i} (X - r_i)$, and such that $r_i - r_j$ is a unit of $S$ whenever $i \neq j$. Let $F \in T[X]$ be a polynomial whose image $f_*F$ satisfies $(f_*F)(r_i) = 0$ for every $i$. The conclusion is that $h$ divides $F$ in $T[X]$. Note that the roots $r_i$ are indexed by $\iota$ with no injectivity hypothesis on $r$ imposed directly; it follows from the unit-difference hypothesis that distinct indices give distinct roots, and the divisibility asserted is in the ring $T[X]$, not merely in $S[X]$.
--
--   This is the standard fact that a monic polynomial which splits with pairwise-separated roots over a faithful extension divides every polynomial vanishing at all those roots, with divisibility descending to the base ring. It is used in the construction of $\Gamma_1$-level links, via [`ModularCurve.IsGamma1Link.of_map_of_surjective_of_ker_pow_eq_bot`](thm.html#ModularCurve.IsGamma1Link.of_map_of_surjective_of_ker_pow_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Polynomial.dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero
    {T : Type u} {S : Type v} [CommRing T] [CommRing S] (f : T →+* S) (hf : Function.Injective f)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : Polynomial T) (hh : h.Monic) (r : ι → S)
    (hsplit : h.map f = ∏ i, (Polynomial.X - Polynomial.C (r i)))
    (hsep : ∀ i j, i ≠ j → IsUnit (r i - r j))
    (F : Polynomial T) (hF : ∀ i, (F.map f).eval (r i) = 0) :
    h ∣ F := by sorry
