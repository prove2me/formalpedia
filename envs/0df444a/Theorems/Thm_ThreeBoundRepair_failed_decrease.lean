-- Prove2me | Theorems.Thm_ThreeBoundRepair_failed_decrease
-- name    : ThreeBoundRepair.failed_decrease
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:41:43.162959+00:00
-- url     : https://prove2.me/theorems/2645c1fe-51a5-4649-8d52-761118404714
-- title:
--   A single-bit guard-count decrease removes exactly one selected failure
-- statement:
--   Fix a stage, a family, a row \(v\), and a level \(l\). If flipping \(((w,c),a)\) strictly decreases the row's failed-guard count, then the selected edge is \(v\to w\) with label \(c\), its guard child changes from true to false, and
--   \[
--   |\operatorname{failed}_l(x,v)|=
--   |\operatorname{failed}_l(x^{\{((w,c),a)\}},v)|+1.
--   \]
--   Thus a strict decrease has a unique location and decreases the count by exactly one.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, GradedRepairCover, lines 47–88; source SHA256 bfcd268a458caa3bfb864a57dc0542e3f1d714ae6c40a6026503f9cbf2c93dab.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
namespace ThreeBoundRepair
end ThreeBoundRepair
open ThreeBoundRepair
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical
variable {L I V : Type} [Fintype V]

theorem ThreeBoundRepair.failed_decrease (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (l : L) (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (hdec : (failed S F l (flip x {((w,c),a)}) v).card < (failed S F l x v).card) :
    S.Adj v w ∧ S.label v w = c ∧
      F (S.guard l) (child x w c) = true ∧
      F (S.guard l) (flip (child x w c) {a}) = false ∧
      (failed S F l x v).card = (failed S F l (flip x {((w,c),a)}) v).card+1 := by sorry
