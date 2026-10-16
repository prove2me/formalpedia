-- Prove2me | Theorems.Thm_PersistClust_Count_nt_empty_push_Y
-- name    : PersistClust.Count.nt_empty_push_Y
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T13:27:40.120646+00:00
-- url     : https://prove2.me/theorems/2550f542-61e7-465b-91b1-d0d29f97ee25
-- title:
--   Emptyness push (Y side): an empty X-stage at level v forces an empty Y-stage at v + eps
-- statement:
--   The interleaving setup: X and Y are one-parameter persistence modules of finite components (comps families with structure maps under filtration laws), phi maps X-levels down eps to Y-levels and psi maps Y-levels down eps to X-levels. If the X-stage is empty at level v (and v + eps is at least alpha), then the Y-stage is empty at v + eps: a point of the Y-stage at v + eps would span a Y-component whose psi-pullback lands in the X-stage at v -- contradicting the emptyness.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the emptyness push (y side) of the interleaving rank calculus. Transcribed GREEN (exit 0, sorry-free) from the working file; the platform mirror structures (comps/structMap/compRep/offD) rely on the platform Definitions via imports.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem nt_empty_push_Y {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    {α ε : ℝ}
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    {v : ℝ} (hv : α ≤ v + ε) (hX : stageX v = ∅) :
    stageY (v + ε) = ∅
    := by sorry
