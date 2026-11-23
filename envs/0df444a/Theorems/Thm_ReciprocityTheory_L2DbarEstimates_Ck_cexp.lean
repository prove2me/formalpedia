-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_cexp
-- name    : ReciprocityTheory.L2DbarEstimates.Ck.cexp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:14.106204+00:00
-- url     : https://prove2.me/theorems/d26689f8-2a4f-4ccc-ae86-1f3cb822e65d
-- title:
--   Ck: cexp
-- statement:
--   The Ck construction uses the cexp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L111-L114

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Ck.cexp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ) (hf : Ck n z k f) :
    Ck n z k (fun x => Complex.exp (f x)) := by sorry
