-- Prove2me | Theorems.Thm_RevenueOrdered_Stackelberg_greedy_card_mono_inter_subset
-- name    : RevenueOrdered.Stackelberg.greedy_card_mono_inter_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:05:49.070055+00:00
-- url     : https://prove2.me/theorems/eefbbe38-66d2-43d4-84d3-71029ba46a59
-- title:
--   Lemma 4.14 — $|\mathrm{greedy}_M(F',L)| \ge |\mathrm{greedy}_M(F,L)|$ and $F\cap\mathrm{greedy}_M(F',L)\subseteq\mathrm{greedy}_M(F,L)$ for $F\subseteq F'$
-- statement:
--   Let $M=(E,\mathcal X)$ be a matroid with finite ground set $E$, and let $L$ be a linear ordering of $E$. For $F\subseteq E$ write $\mathrm{greedy}_M(F,L)$ for the independent subset of $F$ produced by the greedy algorithm run on $F$ in the order induced by $L$. Then for all $F\subseteq F'\subseteq E$:
--
--   1. $|\mathrm{greedy}_M(F',L)|\ge|\mathrm{greedy}_M(F,L)|$, and
--   2. $$F\cap\mathrm{greedy}_M(F',L)\subseteq\mathrm{greedy}_M(F,L).$$
--
--   Enlarging the set on which greedy runs never shrinks its output, and an element of the smaller set that greedy keeps on the larger set is also kept on the smaller set. This is the property behind the regularity axiom (iv) of the choice model of Theorem 4.16.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 23, Lemma 4.14 (proof p. 31)

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy

open Classical

namespace RevenueOrdered.Stackelberg

/-- Lemma 4.14 (Berbeglia–Joret, arXiv:1606.01371v3, p. 23). For a matroid `M` with finite
ground set `E`, a linear ordering `L` of `E`, and `F ⊆ F' ⊆ E`:
(i) `|greedy_M(F', L)| ≥ |greedy_M(F, L)|`, and (ii) `F ∩ greedy_M(F', L) ⊆ greedy_M(F, L)`. -/
theorem greedy_card_mono_inter_subset {α : Type*} (M : Matroid α) (E : Finset α)
    (hE : (E : Set α) = M.E) (L : List α) (hL : IsLinearOrderOf L E)
    (F F' : Finset α) (hFF' : F ⊆ F') (hF'E : F' ⊆ E) :
    (greedyM M L F).card ≤ (greedyM M L F').card ∧
      F ∩ greedyM M L F' ⊆ greedyM M L F := by sorry

end RevenueOrdered.Stackelberg
