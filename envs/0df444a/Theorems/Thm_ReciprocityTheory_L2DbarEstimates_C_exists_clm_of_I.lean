-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_exists_clm_of_I
-- name    : ReciprocityTheory.L2DbarEstimates.C.exists_clm_of_I
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:19.882685+00:00
-- url     : https://prove2.me/theorems/cf69b634-5e79-4c89-9dd4-cfb3f0e67c8e
-- title:
--   C: exists clm of I
-- statement:
--   The C construction uses the exists clm of I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExistsClmOfI.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExistsClmOfI.lean#L8-L17

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExistsClmOfI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open Metric Set Filter Topology Complex
open scoped ContDiff

theorem ReciprocityTheory.L2DbarEstimates.C.exists_clm_of_I {n : ℕ} (A : V n →L[ℝ] ℂ) (hA : ∀ w : V n, A (I • w) = I * A w) :
    ∃ g' : V n →L[ℂ] ℂ, g'.restrictScalars ℝ = A := by sorry
