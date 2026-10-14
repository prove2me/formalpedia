-- Prove2me | Theorems.Thm_PersistClust_Count_sync_comerge_images
-- name    : PersistClust.Count.sync_comerge_images
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T08:22:05.016879+00:00
-- url     : https://prove2.me/theorems/06462a1c-1e95-4afe-82df-df4ca1857752
-- title:
--   Sync-pair co-merge: two X-classes coalescing at level δ have φ-images whose descents both land on the image of the merge
-- statement:
--   Let φ be a level-shifting map from module X to module Y (sending level β to β−ε) that is natural with respect to the structure maps in the sense of the square: for β ≤ β', φ at level β of the descent of a class from β' equals the descent at level β−ε of φ at level β' of the class. Suppose two component classes C₁ and C₂ of X at level u both descend to the same component class E of X at the lower level δ (with δ ≤ u and both levels at least α). Then the φ-images of C₁ and C₂ at level u−ε both descend — at the descent from level u−ε to level δ−ε — to exactly the φ-image of E at level δ−ε. In particular the two image threads co-merge no later than δ−ε.
-- source:
--   SYNC-LOW co-merge packaging of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster; rankKill merge-sync route, design note merge-sync): image threads whose sources co-merge through a level-δ X-merge are one class at δ−ε, so the image merge level is at least δ−ε. Self-contained: takes exactly the interleaving-package hypotheses it needs (φ, hSq1) and nothing else; spliced green from the sibling rankKill lane.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem sync_comerge_images {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {δ u : ℝ} (hδ : α ≤ δ) (hu : α ≤ u) (hle : δ ≤ u)
    (C₁ C₂ : comps stageX JX u) (E : comps stageX JX δ)
    (hm₁ : structMap hLawX hle C₁ = E) (hm₂ : structMap hLawX hle C₂ = E) :
    structMap hLawY (show δ - ε ≤ u - ε by linarith) (φ u hu C₁) = φ δ hδ E ∧
    structMap hLawY (show δ - ε ≤ u - ε by linarith) (φ u hu C₂) = φ δ hδ E
    := by sorry
