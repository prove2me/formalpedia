-- Prove2me | Theorems.Thm_Subgroup_finsum_card_mul_card_fixedBy_quotient_eq_card
-- name    : Subgroup.finsum_card_mul_card_fixedBy_quotient_eq_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/02e87282-d431-5c36-bc2b-b199d575909a
-- title:
--   Artin's counting identity at p-regular elements
-- statement:
--   Let $p$ be a natural number (no primality is assumed), let $G$ be a finite group, and let $b$ be an integer-valued function on the subgroups of $G$. Assume that $b$ satisfies the following normalisation: for every subgroup $H \le G$ that is cyclic and whose order $\operatorname{card} H$ is coprime to $p$, the sum of $b(D)$ over those subgroups $D \le G$ which are cyclic, have order coprime to $p$, and contain $H$, equals $1$ (the sum is written as a finsum over all subgroups of $G$, the summand being $b(D)$ when the three conditions hold and $0$ otherwise). Let $g \in G$ be an element whose order is coprime to $p$. Then the sum over all subgroups $D \le G$ of the quantity $(\operatorname{card} D) \cdot b(D) \cdot \operatorname{card}\bigl((G/D)^{g}\bigr)$, taken to be $0$ unless $D$ is cyclic of order coprime to $p$, equals $\operatorname{card} G$; here $(G/D)^{g}$ denotes the set of points of the left coset space $G/D$ fixed by $g$ under the translation action of $G$.
--
--   This is Artin's induction theorem in its counting form, $\operatorname{card} G \cdot 1_G = \sum_D (\operatorname{card} D)\, b(D)\, \operatorname{Ind}_D^G 1_D$, evaluated at elements of order coprime to $p$, where the values of the induced characters are the numbers of fixed cosets. It is used in the treatment of additive invariants of representations that vanish on inductions from cyclic subgroups of order coprime to $p$, namely by [`Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime`](thm.html#Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_finsum_card_mul_card_fixedBy_quotient_eq_card.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Subgroup.finsum_card_mul_card_fixedBy_quotient_eq_card (p : ℕ) {G : Type} [Group G] [Finite G]
    (b : Subgroup G → ℤ)
    (hb : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p ∧ H ≤ D then b D else 0) = 1)
    (g : G) (hg : (orderOf g).Coprime p) :
    ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p
      then (Nat.card D : ℤ) * b D * Nat.card (MulAction.fixedBy (G ⧸ D) g) else 0) = Nat.card G := by sorry
