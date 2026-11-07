-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_3_6
-- name    : SublinearSteiner.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:44:34.606718+00:00
-- url     : https://prove2.me/theorems/8fa87462-7a73-484b-adb1-8e57ec8ba242
-- title:
--   Lemma 3.6 — a star or a promotion exists
-- statement:
--   Let $K$ be a reduced tree with $E_S(K)\ne\emptyset$ to which no good reconnection applies, and let the tree be rooted at a terminal. Then a short-core star, a small promotion, or a regular promotion exists.
--
--   This is what lets the reduction process continue until it reaches a spanning tree of $T$.
--
--   Differences from the source:
--   - reading: Root K at a terminal → every root terminal; reason: the page names no root; the proof works for any choice
--   - reading: the fan’s parent v′ in a rooted tree → the fringe has the root outside its region; reason: this is what parent means for the page’s rooted tree
--   - generalization: K the current tree of the reduction process of §3.1 (an optimal Steiner tree after good reconnections, events and cleanup) → any feasible tree on T whose nonterminals all have degree at least three (ReducedTree); reason: the proof uses only the tree structure and the absence of good reconnections; every state of the process after cleanup is such a tree
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 3.6, p.18

import Mathlib
import Definitions.Def_SublinearSteiner_ReducedTree

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 3.6, p.18: if `E_S(K) ≠ ∅` and no good reconnection applies, then a short-core star, a small promotion, or
a regular promotion exists.

**Formalization Note.** The page says "Root `K` at a terminal" without choosing one, so the statement holds for every root
terminal. A promotion is witnessed by a fringe for that root. -/
theorem lemma_3_6 {n : ℕ} (w : FinMetric n) (T : Finset (Fin n)) (K : ReducedTree T)
    (hES : K.steinerEdges.Nonempty) (hK : K.NoGoodReconnection w) (root : Fin n) (hroot : root ∈ T) :
    (∃ (v₁ v₂ v₃ : Fin n) (l₁ l₂ l₃ : Limb n), K.IsShortCoreStar w v₁ v₂ v₃ l₁ l₂ l₃) ∨
    (∃ (v v' : Fin n) (l₁ l₂ : Limb n), K.IsFringe w root v v' l₁ l₂ ∧
      ReducedTree.IsSmallPromotion w v l₁ l₂) ∨
    (∃ (v v' : Fin n) (l₁ l₂ : Limb n), K.IsFringe w root v v' l₁ l₂ ∧
      ReducedTree.IsRegularPromotion w v v' l₁ l₂) := by sorry

end SublinearSteiner
