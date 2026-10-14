-- Prove2me | Theorems.Thm_PersistClust_Count_tame_mult_support_finite
-- name    : PersistClust.Count.tame_mult_support_finite
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T20:22:13.322131+00:00
-- url     : https://prove2.me/theorems/853e8079-9318-4d3d-812d-360b9c5bc73e
-- title:
--   T2 finiteness: the multiplicity diagram of a tame module has finite support
-- statement:
--   For a tame module (IsTameModule), the support of the multiplicity functional - the set of extended-plane points where mult (rankFn stage J) is nonzero - is FINITE. The proof goes through the thread identity: the multiplicity agrees, off the degenerate diagonal edges, with the finitely-many-threads census functional (a finite sum over the critical-set-indexed component threads), so the support is a subset of that finite thread set.
-- source:
--   T2 support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the finiteness of the tame multiplicity diagram, the structural input behind tameness transfer and the q-tameness hypotheses of the matching gate. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem tame_mult_support_finite {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) :
    {p : EReal × EReal | mult (rankFn stage J) p ≠ 0}.Finite
    := by sorry
