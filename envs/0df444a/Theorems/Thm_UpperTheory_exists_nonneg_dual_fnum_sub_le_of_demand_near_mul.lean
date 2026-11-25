-- Prove2me | Theorems.Thm_UpperTheory_exists_nonneg_dual_fnum_sub_le_of_demand_near_mul
-- name    : UpperTheory.exists_nonneg_dual_fnum_sub_le_of_demand_near_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:13:08.369675+00:00
-- url     : https://prove2.me/theorems/b5745ce6-62ba-4c3c-9070-fc015778892b
-- title:
--   Upper Theory: exists nonneg dual fnum sub le of demand near mul
-- statement:
--   The Upper Theory construction uses the exists nonneg dual fnum sub le of demand near mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/ExistsNonnegDualFnumSubLeOfDemandNearMul.lean#L9-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/ExistsNonnegDualFnumSubLeOfDemandNearMul.lean#L9-L121

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ExistsMaxFlowAttainedAndIsOptDual
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_SumDemandFilterTwoDivLeOfIsOptDual
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ExistsNonnegDualFnumSubLeOfDemandNearMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.IncomingBounds

theorem UpperTheory.exists_nonneg_dual_fnum_sub_le_of_demand_near_mul :
    ∀ (l d : ℕ) [NeZero d], 5 ≤ l → 2 ≤ d → ∀ (κ : ℝ) (w D : ZMod d → ℝ), 0 < κ → (∀ s, 0 ≤ w s) →
    (∀ s, κ * w s ≤ D s ∧ D s ≤ κ * w s + 4 * w s) →
    ∃ sig : ZMod d → ℝ, (∀ s, 0 ≤ sig s) ∧ IsDualAll l d sig ∧
      Fnum l d (fun s => κ * w s) - κ * (∑ s, w s) / (l : ℝ) ^ 3 - 8 * (∑ s, w s) / l ≤ ∑ s, D s * (gam l - sig s) := by sorry
