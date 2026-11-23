-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_mul
-- name    : ReciprocityTheory.L2DbarEstimates.I.evl_dDot_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:56.51111+00:00
-- url     : https://prove2.me/theorems/ef0e51e3-1ee8-4341-8450-0596f4e782a1
-- title:
--   I: evl d Dot mul
-- statement:
--   The I construction uses the evl d Dot mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L10-L15

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.evl_dDot_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ)
    (hf : Ck n z 1 f) (hg : Ck n z 1 g) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => f y * g y) x ξ = dDot n z f x ξ * g x + f x * dDot n z g x ξ := by sorry
