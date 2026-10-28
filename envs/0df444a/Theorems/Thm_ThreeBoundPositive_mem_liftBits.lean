-- Prove2me | Theorems.Thm_ThreeBoundPositive_mem_liftBits
-- name    : ThreeBoundPositive.mem_liftBits
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:39:48.495149+00:00
-- url     : https://prove2.me/theorems/6b400188-9aba-4772-86ad-2a26becb2fe5
-- title:
--   Membership in a lifted child-coordinate set
-- statement:
--   Let \(s\) be a finite set of child coordinates and let \(\operatorname{liftBits}(v,c,s)\) embed it into child \(c\) of vertex \(v\). Then
--   \[
--   ((w,e),a)\in\operatorname{liftBits}(v,c,s)
--   \quad\Longleftrightarrow\quad w=v,\ e=c,\ a\in s.
--   \]
--   This identifies the support of a child repair set inside the parent coordinates.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, GradedPositiveBoundary, lines 166–178; source SHA256 6d85f6c7ba65c7b083899b73aafdf9256265e82b0d8bcdb147fb371d8519a028.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
namespace ThreeBoundPositive
end ThreeBoundPositive
open ThreeBoundPositive
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

@[simp] theorem ThreeBoundPositive.mem_liftBits (v w : V) (c e : Bool) (a : I) (s : Finset I) :
    ((w,e),a) ∈ liftBits v c s ↔ w = v ∧ e = c ∧ a ∈ s := by sorry
