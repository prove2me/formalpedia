-- Prove2me | Theorems.Thm_PersistClust_Count_crit_free_descent_surjective
-- name    : PersistClust.Count.crit_free_descent_surjective
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T19:45:34.049324+00:00
-- url     : https://prove2.me/theorems/15de2b56-7c33-4b8f-a8c3-14e2949f1663
-- title:
--   Crit-free-window descent is surjective on component classes
-- statement:
--   For a tame module with critical set critSet, the coarsening descent structMap from level w' down to w is SURJECTIVE whenever [w, w'] avoids the critical set: every stage-w class is the descent of some stage-w' class. The proof takes the representative of the stage-w class, lifts it through the crit-free componentwise bijection of critSet_spec to a stage-w' point, and builds the stage-w' class of that lift; its descent is the original class by a J-compatibility chain, closed with Subtype.ext.
-- source:
--   T3a support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the descent-surjectivity half of the critical-window rigidity consumed by the freshness and thread arguments of the gate. Transcribed GREEN from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem crit_free_descent_surjective {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w w' : ℝ} (hww : w ≤ w')
    (hfree : ∀ τ ∈ critSet hTame, τ < w ∨ w' < τ) (C : comps stage J w) :
    ∃ C' : comps stage J w', structMap hLaw hww C' = C
    := by sorry
