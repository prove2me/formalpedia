-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
-- name    : ReciprocityTheory.L2DbarEstimates.Ck.add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:26.23253+00:00
-- url     : https://prove2.me/theorems/b28b29b9-5000-412b-83b1-eaf4e1c15aef
-- title:
--   Ck: add
-- statement:
--   The Ck construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L92-L94

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

theorem ReciprocityTheory.L2DbarEstimates.Ck.add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f g : M → ℂ) (hf : Ck n z k f) (hg : Ck n z k g) :
    Ck n z k (fun x => f x + g x) := by sorry
