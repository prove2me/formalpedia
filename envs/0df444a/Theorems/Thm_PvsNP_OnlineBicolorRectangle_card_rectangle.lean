-- Prove2me | Theorems.Thm_PvsNP_OnlineBicolorRectangle_card_rectangle
-- name    : PvsNP.OnlineBicolorRectangle.card_rectangle
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T04:15:20.723673+00:00
-- url     : https://prove2.me/theorems/3f7cf007-f613-5dcf-b526-cc6aa396203f
-- title:
--   Rectangle capacity for balanced partitions of bicolored disjointness
-- statement:
--   Let V be a finite value alphabet. In a rectangle of input assignments, each row has a red positions and c blue positions, and each column has c red positions and a blue positions. Suppose every pairing in the rectangle has no common value between the red row positions and the blue column positions and no common value between the blue row positions and the red column positions. Then four to the power a+c times the number of pairs in the rectangle is at most the size of V to the power 2(a+c).
-- source:
--   A deterministic rectangle bound for an application of the crossing-sequence method of Kalyanasundaram and Schnitger, https://doi.org/10.1007/978-3-322-95233-2_15.

import Mathlib

theorem PvsNP.OnlineBicolorRectangle.card_rectangle {V : Type*} [DecidableEq V] [Fintype V] {a c : ℕ}
    (left : Finset ((Fin a → V) × (Fin c → V)))
    (right : Finset ((Fin c → V) × (Fin a → V)))
    (redLeft : ∀ x ∈ left, ∀ y ∈ right, ∀ i j, x.1 i ≠ y.2 j)
    (blueLeft : ∀ x ∈ left, ∀ y ∈ right, ∀ i j, x.2 i ≠ y.1 j) :
    4^(a+c) * (left.card * right.card) ≤ Fintype.card V^(2*(a+c)) := by sorry
