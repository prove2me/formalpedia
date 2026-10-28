-- Prove2me | Theorems.Thm_ThreeBoundConditional_strict_repair_cases
-- name    : ThreeBoundConditional.strict_repair_cases
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:42:13.654063+00:00
-- url     : https://prove2.me/theorems/ee1b191c-36e2-46c3-a732-0b3d80af6f66
-- title:
--   A zero-tolerance row is repaired at its sole target or sole guard defect
-- statement:
--   Suppose a zero-tolerance ordinary row \(v\) is false before a single flip and true afterwards. Then either the flip is in its own child, that child is the unique failed target, and the old guard-failure set is empty; or both old targets are true and the old guard-failure set is exactly \(\{w\}\), where the flipped child is selected by the edge \(v\to w\). In the second case the selected guard changes from true to false. This precisely classifies the strict-row repair positions.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, StrictUnion, lines 85–165; source SHA256 b8cb65cdc129887eb3729182f514b30c59d50d82acb433874b9fc2b49ed81538.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_StrictUnion
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
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace ThreeBoundConditional
end ThreeBoundConditional
open ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem ThreeBoundConditional.strict_repair_cases (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (hoff : ¬ordinaryRow S F t g 0 x v)
    (hon : ordinaryRow S F t g 0 (flip x {((w,c),a)}) v) :
    (w=v ∧ F t (child x v c)=false ∧
      (∀ e : Bool, e ≠ c → F t (child x v e)=true) ∧
      guardFailures S F g x v = ∅ ∧ F t (flip (child x v c) {a})=true) ∨
    ((∀ e : Bool, F t (child x v e)=true) ∧ guardFailures S F g x v = {w} ∧
      S.Adj v w ∧ S.label v w=c ∧ F g (child x w c)=true ∧
      F g (flip (child x w c) {a})=false) := by sorry
