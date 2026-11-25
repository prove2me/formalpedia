-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_db_eq_zero_of_notMem
-- name    : ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.db_eq_zero_of_notMem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:53.35191+00:00
-- url     : https://prove2.me/theorems/f9d26b32-bda1-4b25-8bfc-ef2e628b7f17
-- title:
--   Chart Wirtinger Derivatives: db eq zero of not Mem
-- statement:
--   The Chart Wirtinger Derivatives construction uses the db eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L165-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L165-L178

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.db_eq_zero_of_notMem {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (hx : x ∉ tsupport f) : db n z j f x = 0 := by sorry
