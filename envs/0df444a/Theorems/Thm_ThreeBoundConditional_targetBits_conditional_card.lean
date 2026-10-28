-- Prove2me | Theorems.Thm_ThreeBoundConditional_targetBits_conditional_card
-- name    : ThreeBoundConditional.targetBits_conditional_card
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:41:01.528055+00:00
-- url     : https://prove2.me/theorems/3865efe8-d833-4fe0-803a-7b796b0650a4
-- title:
--   Two target children have a refined conditional downward cost
-- statement:
--   Consider two children that are both true at level \(t_j\), with at least one false at level \(t_k\). If \(M_F(t_i,t_j,t_k)\le m\) and \(B_F(t_i,t_k)\le b\), then
--   \[
--   |\operatorname{targetBits}(F,t_i,x,v)|\le\max(2m,m+b).
--   \]
--   This improves the unconditional sum of two downward bounds when a later target is known to fail.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ConditionalOrdinary, lines 117–137; source SHA256 f3399d34ca31ad9b4ad9de5a4ab294181bbd230bb91c7ec217c0414e4e592080.

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
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
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
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace ThreeBoundConditional
end ThreeBoundConditional
open ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem ThreeBoundConditional.targetBits_conditional_card (F : L → (I → Bool) → Bool)
    (ti tj tk : L) (x : ((V × Bool) × I) → Bool) (v : V) (m b : ℕ)
    (hm : MBound F ti tj tk m) (hb : BBound F ti tk b)
    (ht : ∀ c : Bool, F tj (child x v c) = true)
    (hmiss : ∃ c : Bool, F tk (child x v c) = false) :
    (targetBits F ti x v).card ≤ max (2*m) (m+b) := by sorry
