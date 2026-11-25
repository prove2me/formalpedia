-- Prove2me | Theorems.Thm_UpperTheory_sum_demand_filter_two_div_le_of_isOptDual
-- name    : UpperTheory.sum_demand_filter_two_div_le_of_isOptDual
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:11.286649+00:00
-- url     : https://prove2.me/theorems/a042fd73-aab6-5146-98f8-481d29314c12
-- title:
--   Upper Theory: sum demand filter two div le of is Opt Dual
-- statement:
--   The Upper Theory construction uses the sum demand filter two div le of is Opt Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/SumDemandFilterTwoDivLeOfIsOptDual.lean#L9-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/SumDemandFilterTwoDivLeOfIsOptDual.lean#L9-L56

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ExistsMaxFlowAttainedAndIsOptDual
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_SumDemandFilterTwoDivLeOfIsOptDual
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

theorem UpperTheory.sum_demand_filter_two_div_le_of_isOptDual :
    ∀ (l d : ℕ) [NeZero d], 3 ≤ l → ∀ D sig : ZMod d → ℝ, 0 ≤ D → IsOptDual l d D sig →
    (∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s) ≤ (∑ s : ZMod d, D s) / l := by sorry
