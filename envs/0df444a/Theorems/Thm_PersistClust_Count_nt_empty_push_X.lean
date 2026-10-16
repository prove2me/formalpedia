-- Prove2me | Theorems.Thm_PersistClust_Count_nt_empty_push_X
-- name    : PersistClust.Count.nt_empty_push_X
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T13:29:28.538273+00:00
-- url     : https://prove2.me/theorems/4b2b6486-4328-4115-adce-8109d0585965
-- title:
--   Emptyness push (X side): an empty Y-stage at level u forces an empty X-stage at u + eps
-- statement:
--   The interleaving setup: X and Y are one-parameter persistence modules of finite components (comps families with structure maps under filtration laws), phi maps X-levels down eps to Y-levels and psi maps Y-levels down eps to X-levels. If the Y-stage is empty at level u (and u + eps is at least alpha), then the X-stage is empty at u + eps: a point of the X-stage at u + eps would span an X-component whose phi-pullback lands in the Y-stage at u -- contradicting the emptyness.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the emptyness push (x side) of the interleaving rank calculus. Transcribed GREEN (exit 0, sorry-free) from the working file; the platform mirror structures (comps/structMap/compRep/offD) rely on the platform Definitions via imports.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem nt_empty_push_X {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    {u : ℝ} (hu : α ≤ u + ε) (hY : stageY u = ∅) :
    stageX (u + ε) = ∅
    := by sorry
