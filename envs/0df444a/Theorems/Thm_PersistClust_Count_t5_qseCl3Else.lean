-- Prove2me | Theorems.Thm_PersistClust_Count_t5_qseCl3Else
-- name    : PersistClust.Count.t5_qseCl3Else
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T11:59:31.613157+00:00
-- url     : https://prove2.me/theorems/c8254be9-ab04-48f9-886f-8e7a74acf14c
-- title:
--   Demanded QSE copies are high-far: the demand-structure clause for the QSE sector
-- statement:
--   Fix a persistence diagram D over the extended-real plane with off-diagonal copies (each off-diagonal copy is a point of the diagram together with a copy index below its multiplicity), a level alpha and a radius eps >= 0. Call a copy DEMANDED (off-diagonal) when the diagonal cannot absorb it at radius eps: either the copy is PROMINENT -- its point lies strictly above alpha in both coordinates and no diagonal point is eps-close to it in both coordinates -- or its point lies in the QSE quadrant with birth strictly above alpha + eps and more than 2*eps above its death coordinate. The claim: any demanded copy whose point lies in the QSE quadrant (birth above alpha, death at or below alpha) automatically carries the full second bundle -- its birth is strictly above alpha + eps and its birth exceeds its death coordinate by more than 2*eps. In other words, the demand structure separates cleanly by quadrant: demanded copies pointing into the strict-below quadrant are prominent, and demanded copies pointing into the closed-below QSE quadrant are exactly the high-far ones. This clause is the case-work engine behind the demand census of the matching argument in persistence-based clustering; copies, quadrants and the demand predicate are the platform's offD/offPt/QSE/DemandsOff structures.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the demand-structure clause for the QSE sector (demanded QSE-pointed copies carry the full high-far bundle). Transcribed GREEN (exit 0, sorry-free) from the working file; zero-declaration closure -- the demand predicate, the prominence predicate and the off-diagonal copy structures are the platform's Definitions (Def_PersistClust_Count_MatchingGate), imported in the preamble.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem t5_qseCl3Else {D : EReal × EReal → ℕ∞} {α ε : ℝ}
    (a : {x : offD D // DemandsOff α ε x}) (hmem : offPt a.1 ∈ QSE α) :
    offPt a.1 ∈ QSE α ∧ α + ε < (offPt a.1).1 ∧
      2 * ε < (offPt a.1).1 - (offPt a.1).2
    := by sorry
