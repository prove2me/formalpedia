-- Prove2me | Theorems.Thm_ThreeBoundConditional_ordinaryGuardBits_card_special
-- name    : ThreeBoundConditional.ordinaryGuardBits_card_special
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:40:48.268609+00:00
-- url     : https://prove2.me/theorems/ebc4df68-f16d-4cd7-9ce2-be72ad915b34
-- title:
--   A conditioned passing guard improves one term of the guard cost
-- statement:
--   In the ordinary guard-bit setting, suppose a particular passing guard selects a child that is also true at level \(g_k\). If \(A_F(g_j,g_i)\le a\) and \(P_F(g_k,g_j,g_i)\le p\), then
--   \[
--   |\operatorname{ordinaryGuardBits}|
--   \le\bigl(d^+(v)-f_{g_j}(v)-1\bigr)a+p.
--   \]
--   The additional true condition replaces one ordinary upward charge by the conditional charge \(p\).
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ConditionalOrdinary, lines 182–211; source SHA256 f3399d34ca31ad9b4ad9de5a4ab294181bbd230bb91c7ec217c0414e4e592080.

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

theorem ThreeBoundConditional.ordinaryGuardBits_card_special (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (gi gj gk : L) (x : ((V × Bool) × I) → Bool) (v w : V) (a p : ℕ)
    (ha : ABound F gj gi a) (hp : PBound F gk gj gi p)
    (hw : w ∈ passingGuards S F gj x v)
    (hk : F gk (child x w (S.label v w)) = true) :
    (ordinaryGuardBits S F gi gj x v).card ≤
      ((outgoing S v).card - (guardFailures S F gj x v).card - 1)*a+p := by sorry
