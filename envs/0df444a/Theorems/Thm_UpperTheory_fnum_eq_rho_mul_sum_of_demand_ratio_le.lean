-- Prove2me | Theorems.Thm_UpperTheory_fnum_eq_rho_mul_sum_of_demand_ratio_le
-- name    : UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:28.715443+00:00
-- url     : https://prove2.me/theorems/93d0b80e-642a-4921-a51d-928fc127f2c1
-- title:
--   Upper Theory: fnum eq rho mul sum of demand ratio le
-- statement:
--   The Upper Theory construction uses the fnum eq rho mul sum of demand ratio le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/FnumEqRhoMulSumOfDemandRatioLe.lean#L139-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/FnumEqRhoMulSumOfDemandRatioLe.lean#L139-L185

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_FnumEqRhoMulSumOfDemandRatioLe
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
open UpperTheory.AlternatingNumberFlow

theorem UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le :
    ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → ∀ D : ZMod d → ℝ, 0 ≤ D →
    (∀ s s' : ZMod d, D s' ≤ (l : ℝ) * D s) → Fnum l d D = rho l * (∑ s : ZMod d, D s) := by sorry
