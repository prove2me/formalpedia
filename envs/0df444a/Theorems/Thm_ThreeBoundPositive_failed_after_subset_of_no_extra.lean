-- Prove2me | Theorems.Thm_ThreeBoundPositive_failed_after_subset_of_no_extra
-- name    : ThreeBoundPositive.failed_after_subset_of_no_extra
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:40:03.269995+00:00
-- url     : https://prove2.me/theorems/72baf157-370f-4c49-9e51-528d7c68ab37
-- title:
--   Without a new failure, the old strong guard set covers the new weak one
-- statement:
--   Let \(F\) be nested, and let stage levels \(i,j\) satisfy \(\operatorname{guard}(j)\le\operatorname{guard}(i)\). Fix a row and a single child-bit flip. If that flip creates no extra weak guard failure at a location that previously passed the strong guard test, then
--   \[
--   \operatorname{failed}_i(x^{\{a\}})\subseteq\operatorname{failed}_j(x).
--   \]
--   This inclusion controls changes in the guard count when bounding positive-boundary sensitivity.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, GradedPositiveBoundary, lines 44–64; source SHA256 6d85f6c7ba65c7b083899b73aafdf9256265e82b0d8bcdb147fb371d8519a028.

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

theorem ThreeBoundPositive.failed_after_subset_of_no_extra (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (hg : S.guard j ≤ S.guard i)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (he : ¬ ExtraFailure S F i j x v w c a) :
    failed S F i (flip x {((w,c),a)}) v ⊆ failed S F j x v := by sorry
