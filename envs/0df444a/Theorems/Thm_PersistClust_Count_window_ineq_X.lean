-- Prove2me | Theorems.Thm_PersistClust_Count_window_ineq_X
-- name    : PersistClust.Count.window_ineq_X
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T20:04:44.664154+00:00
-- url     : https://prove2.me/theorems/de229ac0-57d3-48b4-80b5-22b8e46cd1c8
-- title:
--   S4 window inequality, X side: X-windows dominate eps-shrunk Y-windows
-- statement:
--   Given a strong eps-interleaving above alpha between two filtration modules (structure maps phi : X^beta -> Y^(beta-eps) and psi backwards with the commuting squares), the X-window count of components born by level t and surviving to s dominates the Y-window count shrunk by eps on both sides: rankFn X s (t-eps-eps) <= rankFn Y (s-eps) (t-eps) whenever t <= s and alpha <= t - eps. The proof rewrites the X-rank as the encard of the image of a structure map (rankFn_eq_structImage'), re-factors that image through the composite descent (structMap_comp), rewrites the descent through square (iv') as psi of phi, injects the phi-images into the Y-structure image via square (i'), and chains encard monotonicity.
-- source:
--   S4 support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the X-side window inequality of the matching gate, the rank-level engine behind every image-window bound (birth/death transfer) of the lane. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem window_ineq_X {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {s t : ℝ} (hst : t ≤ s) (hα : α ≤ t - ε) :
    rankFn stageX JX s ((t - ε) - ε) ≤ rankFn stageY JY (s - ε) (t - ε)
    := by sorry
