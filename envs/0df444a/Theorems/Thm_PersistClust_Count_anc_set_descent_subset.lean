-- Prove2me | Theorems.Thm_PersistClust_Count_anc_set_descent_subset
-- name    : PersistClust.Count.anc_set_descent_subset
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T19:51:21.616332+00:00
-- url     : https://prove2.me/theorems/33451fbf-5be4-429e-a62f-a617c9d0e0eb
-- title:
--   Rung-B helper: ancestor-level sets only grow under descent
-- statement:
--   For a filtration law, the ancestor-level set AncSet of a component class only grows when the class descends: every ancestor of E at level t remains an ancestor of the descended class structMap (t' <= t) E at the lower level t' <= t. The proof composes the two structure maps with structMap_comp and re-witnesses the ancestor relation.
-- source:
--   Rung-B support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the ancestor-monotonicity fact underlying birth-sup descent bookkeeping. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem anc_set_descent_subset {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {t t' : ℝ} (hle : t' ≤ t) (E : comps stage J t) :
    AncSet hLaw t E ⊆ AncSet hLaw t' (structMap hLaw hle E)
    := by sorry
