-- Prove2me | Theorems.Thm_PersistClust_Count_qse_member_demands_high_far
-- name    : PersistClust.Count.qse_member_demands_high_far
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T16:28:40.753889+00:00
-- url     : https://prove2.me/theorems/ac02766f-43e9-41aa-8782-c2cf9397add4
-- title:
--   QSE members of the demand sector are high-far (DemandsOff clause-3 else)
-- statement:
--   Let a be an off-diagonal copy of a multiplicity diagram D that the diagonal cannot absorb at radius eps (DemandsOff alpha eps a: a is either a prominent QNE copy, or a QSE copy that is high-far — born above alpha + eps and more than 2*eps above the diagonal), and suppose the off-diagonal point offPt a lies in the quadrant QSE alpha (birth coordinate strictly above alpha, death coordinate at most alpha). Then the high-far QSE prong of the DemandsOff disjunction holds for a: offPt a lies in QSE alpha, the birth coordinate of offPt a exceeds alpha + eps, and the birth coordinate exceeds the death coordinate by more than 2*eps. The prominent-QNE prong is impossible for a QSE point: PromQNE would place offPt a in the quadrant QNE alpha with BOTH coordinates strictly above alpha, while QSE alpha bounds the second coordinate by alpha — the quadrants are definitionally disjoint in the second coordinate.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the clause-3 else-case engine of the qseInjection routing theorem — separating the QSE-prong priority routing from the prominent-copy sector: every DemandsOff member whose point lies in QSE must be a high-far QSE copy (birth above alpha+eps, more than 2*eps above the diagonal).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem qse_member_demands_high_far {D : EReal × EReal → ℕ∞} {α ε : ℝ}
    (a : {x : offD D // DemandsOff α ε x}) (hmem : offPt a.1 ∈ QSE α) :
    offPt a.1 ∈ QSE α ∧ α + ε < (offPt a.1).1 ∧
      2 * ε < (offPt a.1).1 - (offPt a.1).2
    := by sorry
