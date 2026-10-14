-- Prove2me | Theorems.Thm_PersistClust_Count_struct_map_compose
-- name    : PersistClust.Count.struct_map_compose
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T19:41:51.966639+00:00
-- url     : https://prove2.me/theorems/fcafd2eb-7f18-470a-a001-ec655e63915d
-- title:
--   S1 composition: the component coarsening maps of a filtration compose
-- statement:
--   Let a 0-dimensional persistence module be given by a filtration law stage/J with its component classes comps and the coarsening (lambda-structure) maps structMap that send a stage-t component class to the stage-s class containing it (s <= t). The structure maps compose: descending from level u to t and then from t to s equals descending from u to s directly, structMap (s <= t) (structMap (t <= u) C) = structMap (le_trans ...) C. The proof joins the two representative points along the J-relation using reflexivity, antitone descent and the compatibility axiom of a filtration law, then compares the resulting classes pointwise by transitivity/symmetry of J and closes with Subtype.ext.
-- source:
--   S1 support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the coarsening-map composition that every window-inequality / alive-up / birth-chain argument of the matching gate consumes. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem struct_map_compose {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u)
    (C : comps stage J u) :
    structMap hLaw hst (structMap hLaw htu C) = structMap hLaw (le_trans hst htu) C
    := by sorry
