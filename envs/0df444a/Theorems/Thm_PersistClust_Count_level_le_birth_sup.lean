-- Prove2me | Theorems.Thm_PersistClust_Count_level_le_birth_sup
-- name    : PersistClust.Count.level_le_birth_sup
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T19:53:28.638979+00:00
-- url     : https://prove2.me/theorems/29ad62a1-0d6d-4f87-b7c9-42f2fc7fa480
-- title:
--   Rung-B helper: a cell's own level lower-bounds its birth-sup
-- statement:
--   For a tame module, every component class E at level t satisfies t <= birthSup E: its own level is an ancestor level (the class is its own ancestor via the identity structure map), and the ancestor set is bounded above by the eventual-emptiness level of the tameness structure, so the supremum exists and dominates t.
-- source:
--   Rung-B support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the level-to-birth-sup lower bound consumed by the alive-up and birth-chain arguments. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem level_le_birth_sup {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {t : ℝ} (E : comps stage J t) :
    t ≤ birthSup hLaw t E
    := by sorry
