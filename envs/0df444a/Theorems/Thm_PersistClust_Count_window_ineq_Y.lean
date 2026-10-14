-- Prove2me | Theorems.Thm_PersistClust_Count_window_ineq_Y
-- name    : PersistClust.Count.window_ineq_Y
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T20:08:37.90942+00:00
-- url     : https://prove2.me/theorems/30bdfcdd-ebb9-411c-9b42-34aeffabc3f5
-- title:
--   S4 window inequality, Y side: Y-windows dominate eps-shrunk X-windows
-- statement:
--   The mirror of the X-side window inequality: given a strong eps-interleaving above alpha, the Y-window count of components born by level t and surviving to s dominates the X-window count shrunk by eps: rankFn Y s (t-eps-eps) <= rankFn X (s-eps) (t-eps). The proof is the same rank-to-image reduction on the Y side, using squares (ii') and (iii') instead of (i') and (iv').
-- source:
--   S4 support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the Y-side window inequality of the matching gate, the mirror engine of window_ineq_X. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem window_ineq_Y {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {s t : ℝ} (hst : t ≤ s) (hα : α ≤ t - ε) :
    rankFn stageY JY s ((t - ε) - ε) ≤ rankFn stageX JX (s - ε) (t - ε)
    := by sorry
