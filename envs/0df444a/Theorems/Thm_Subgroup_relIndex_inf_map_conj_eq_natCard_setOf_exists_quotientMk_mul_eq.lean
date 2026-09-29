-- Prove2me | Theorems.Thm_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq
-- name    : Subgroup.relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/440b2111-4047-5faf-9c47-37a721b6fa72
-- title:
--   Index of K∩ gKg⁻¹ counts K-cosets in KgK
-- statement:
--   Let $G$ be a group, $K\le G$ a subgroup and $g\in G$ an element. Write $gKg^{-1}$ for the image `K.map (MulAut.conj g).toMonoidHom` of $K$ under conjugation by $g$. The assertion is that the relative index of $K\cap gKg^{-1}$ in $K$ — in Mathlib's sense, the index of the subgroup $(K\cap gKg^{-1})\cap K$ viewed inside $K$ — coincides with the cardinality, as a natural number, of the set of those classes $c$ in the left-coset quotient $G/K$ for which there exists $k\in K$ with $kg\equiv c$, i.e. with $c=kgK$. Both sides are natural numbers with the usual convention that an infinite index and an infinite cardinality are both recorded as $0$, so the equality holds with no finiteness hypothesis on $G$, on $K$ or on the index. The right-hand side is thus the number of left $K$-cosets contained in the double coset $KgK$.
--
--   This is the orbit–stabiliser count for the action of $K$ on $G/K$ by left translation: the stabiliser of the class of $g$ is $K\cap gKg^{-1}$ and its orbit is the set of cosets inside $KgK$, so the relative index is the degree of the double coset. It serves as the group-theoretic dictionary between relative indices of intersections of a subgroup with a conjugate and the number of cosets in a double coset, and is used in the computation of local indices for stabilisers of Eichler orders and of the degrees occurring in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Subgroup.relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq
    {G : Type*} [Group G] (K : Subgroup G) (g : G) :
    (K ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex K =
      Nat.card {c : G ⧸ K // ∃ k ∈ K, (QuotientGroup.mk (k * g) : G ⧸ K) = c} := by sorry
