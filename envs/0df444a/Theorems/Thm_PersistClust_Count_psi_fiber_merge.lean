-- Prove2me | Theorems.Thm_PersistClust_Count_psi_fiber_merge
-- name    : PersistClust.Count.psi_fiber_merge
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T13:33:15.742152+00:00
-- url     : https://prove2.me/theorems/e4c2dbd7-9b68-4531-9cc7-4b53e67e4634
-- title:
--   Psi-fiber merge (square iii'): psi-identified Y-cells have equal 2eps-descent structure maps
-- statement:
--   The interleaving setup: X and Y are one-parameter persistence modules of finite components (comps families with structure maps under filtration laws), phi maps X-levels down eps to Y-levels and psi maps Y-levels down eps to X-levels. Assume the square law (iii'): phi at the pullback level of the psi-image of any Y-cell y equals the 2eps-descent structure map of y. If psi identifies two Y-cells y and y' at a common level beta at least alpha (with the pullback level also at least alpha), then the 2eps-descent structure maps of y and y' agree: the psi-fiber carries the equality down to the source descent.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the psi-fiber merge (square iii') of the interleaving rank calculus. Transcribed GREEN (exit 0, sorry-free) from the working file; the platform mirror structures (comps/structMap/compRep/offD) rely on the platform Definitions via imports.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem psi_fiber_merge {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {β : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε) {y y' : comps stageY JY β}
    (hψ : ψ β hβ y = ψ β hβ y') :
    structMap hLawY (show (β - ε) - ε ≤ β by linarith) y =
      structMap hLawY (show (β - ε) - ε ≤ β by linarith) y'
    := by sorry
