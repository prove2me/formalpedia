-- Prove2me | Theorems.Thm_ThreeBoundConditional_ordinaryGuardBits_card_le
-- name    : ThreeBoundConditional.ordinaryGuardBits_card_le
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:40:28.666477+00:00
-- url     : https://prove2.me/theorems/13f22fdf-5210-4786-bb53-c5edfcd10d65
-- title:
--   Passing guards contribute at most one upward profile each
-- statement:
--   Fix a stage, an input, and a row \(v\). Let \(d^+(v)\) be its outgoing degree and \(f_{g_j}(v)\) the number of failed guards at level \(g_j\). If the child upward profile \(A_F(g_j,g_i)\) is bounded by \(a\), then the ordinary guard-destruction bit set satisfies
--   \[
--   |\operatorname{ordinaryGuardBits}|
--   \le \bigl(d^+(v)-f_{g_j}(v)\bigr)a.
--   \]
--   Each contributing child is selected by a currently passing guard. This bounds the guard part of a downward parent profile.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ConditionalOrdinary, lines 165–180; source SHA256 f3399d34ca31ad9b4ad9de5a4ab294181bbd230bb91c7ec217c0414e4e592080.

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

theorem ThreeBoundConditional.ordinaryGuardBits_card_le (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (gi gj : L) (x : ((V × Bool) × I) → Bool) (v : V) (a : ℕ)
    (ha : ABound F gj gi a) :
    (ordinaryGuardBits S F gi gj x v).card ≤
      ((outgoing S v).card - (guardFailures S F gj x v).card)*a := by sorry
