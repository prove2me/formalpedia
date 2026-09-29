-- Prove2me | Theorems.Thm_RingHom_eq_of_forall_exists_sub_mem_pow_of_comp_eq
-- name    : RingHom.eq_of_forall_exists_sub_mem_pow_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/8427325d-5679-55cb-a41c-36523930f9cb
-- title:
--   Uniqueness of ring maps agreeing on a dense subring
-- statement:
--   Let $R$, $\hat R$, $S$ be commutative rings, let $\iota : R \to \hat R$ be a ring homomorphism and let $I \subseteq \hat R$ be an ideal. Assume the image of $\iota$ is $I$-adically dense, in the sense that for every $x \in \hat R$ and every natural number $n$ there is $r \in R$ with $x - \iota(r) \in I^{n}$. Let $J \subseteq S$ be an ideal for which $S$ is $J$-adically Hausdorff in Mathlib's sense (`IsHausdorff J S`): an element of $S$ congruent to $0$ modulo $J^{n} \cdot \top$ for every $n$ is $0$, i.e. $\bigcap_n J^{n} = 0$. Let $G, H : \hat R \to S$ be ring homomorphisms which both carry $I$ into $J$, that is $G(x) \in J$ and $H(x) \in J$ for all $x \in I$. Then if $G \circ \iota = H \circ \iota$ as ring homomorphisms $R \to S$, one has $G = H$.
--
--   This is the algebraic form of the uniqueness of a continuous extension to a completion: a map out of an $I$-adically dense subring is determined by its restriction, provided the target is separated and the maps are continuous in the weak sense that $I$ goes into $J$. It is used in the construction of local charts on Drinfeld and modular curves, to identify two ring homomorphisms out of a chart ring that agree on the image of the uncompleted ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_eq_of_forall_exists_sub_mem_pow_of_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingHom.eq_of_forall_exists_sub_mem_pow_of_comp_eq
    (R Rh S : Type) [CommRing R] [CommRing Rh] [CommRing S]
    (ι : R →+* Rh) (I : Ideal Rh)
    (hdense : ∀ (x : Rh) (n : ℕ), ∃ r : R, x - ι r ∈ I ^ n)
    (J : Ideal S) [IsHausdorff J S]
    (G H : Rh →+* S) (hG : ∀ x ∈ I, G x ∈ J) (hH : ∀ x ∈ I, H x ∈ J)
    (h : G.comp ι = H.comp ι) :
    G = H := by sorry
