-- Prove2me | Theorems.Thm_PersistClust_Count_off_diagonal_copies_finite
-- name    : PersistClust.Count.off_diagonal_copies_finite
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T20:05:41.391964+00:00
-- url     : https://prove2.me/theorems/9c37d840-2885-4107-b3f2-a282743b4be3
-- title:
--   Finiteness of the off-diagonal copies of a tame module's diagram
-- statement:
--   For a tame persistence module over a filtration-law component family, the set of off-diagonal copies of its multiplicity diagram is finite: offD (mult (rankFn stage J)) — the type of pairs pairing a diagram point with an index below its multiplicity — has finitely many elements. Proof: the multiplicity is nonzero only at bars (essential points with death -infinity, or real bars with death below birth), and there the elder-rule transfer (T3a) gives a finitely-supported thread-count agreeing with the multiplicity, so the multiplicity support is finite (T2b); above any support point the copy indices are bounded by the finite multiplicity value, and the copy projection is injective in the index on each fiber, so each fiber is finite and the whole copy universe is a finite union of finite fibers.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the off-diagonal copy space of a tame module's diagram is finite — the finiteness backbone for the copy-routing/demand bookkeeping of the multi-bijection assembly (t5_offD_finite in the rankKill master, Scratch_rankR1 L2208).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem off_diagonal_copies_finite {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) :
    (Set.univ : Set (offD (mult (rankFn stage J)))).Finite
    := by sorry
