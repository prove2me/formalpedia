-- Prove2me | Theorems.Thm_PositiveSeparation
-- name    : PositiveSeparation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:17:51.95425+00:00
-- url     : https://prove2.me/theorems/de8cebaa-66d0-4899-97b5-0cdc3bbba037
-- title:
--   Positive separation of disjoint nonempty compact sets
-- statement:
--   If $A$ and $B$ are nonempty, disjoint compact subsets of the Euclidean plane, then they have positive mutual separation:
--   $$
--   \exists \delta>0,\quad orall a\in A\ orall b\in B,\quad \delta\le d(a,b).
--   $$
--
--   This is the compactness lemma that turns disjointness of the old prefix region and the polygonal tail into a uniform distance bound.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PositiveSeparation.lean#L1-31

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact

open Classical
noncomputable section

lemma PositiveSeparation {A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : A.Nonempty) (hB : B.Nonempty) (hAc : IsCompact A) (hBc : IsCompact B)
    (hdisj : Disjoint A B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a, a ∈ A → ∀ b, b ∈ B → δ ≤ dist a b := by sorry
