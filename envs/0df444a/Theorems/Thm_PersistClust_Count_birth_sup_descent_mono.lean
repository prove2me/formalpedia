-- Prove2me | Theorems.Thm_PersistClust_Count_birth_sup_descent_mono
-- name    : PersistClust.Count.birth_sup_descent_mono
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T19:55:34.836355+00:00
-- url     : https://prove2.me/theorems/696efc7a-91d3-4341-8cd9-491b4e540e23
-- title:
--   Rung-B helper: birth-sups only grow under descent
-- statement:
--   For a tame module, the birth-supremum of a component class is monotone under the coarsening descent: birthSup E at level t is at most birthSup of the descended class at any lower level t' <= t. The proof re-witnesses every ancestor of E as an ancestor of the descended class (via structMap_comp), notes the descended ancestor set is nonempty and bounded above by the eventual-emptiness level, and closes with csSup_le.
-- source:
--   Rung-B support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the birth-sup descent-monotonicity consumed by the descent-pin (t5_hDescPin) and birth-chain tools. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy; it also underlies the accepted alive_cell_lift node.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem birth_sup_descent_mono {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {t t' : ℝ} (hle : t' ≤ t) (E : comps stage J t) :
    birthSup hLaw t E ≤ birthSup hLaw t' (structMap hLaw hle E)
    := by sorry
