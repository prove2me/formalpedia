-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_cexp
-- name    : ReciprocityTheory.L2DbarEstimates.d_cexp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:31.46135+00:00
-- url     : https://prove2.me/theorems/3071e623-2b42-5eb7-bab3-ebe8041ec5b7
-- title:
--   L2 Dbar Estimates: d cexp
-- statement:
--   The L2 Dbar Estimates construction uses the d cexp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L310-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L310-L318

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

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

theorem ReciprocityTheory.L2DbarEstimates.d_cexp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Ck n z 1 f) (j : Fin n) (x : M) :
    d n z j (fun y => Complex.exp (f y)) x = Complex.exp (f x) * d n z j f x := by sorry
