-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
-- name    : ReciprocityTheory.L2DbarEstimates.Ck.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:35.940722+00:00
-- url     : https://prove2.me/theorems/278f3b85-afe8-49a1-9e8f-09ff6d6e0741
-- title:
--   Ck: mono
-- statement:
--   The Ck construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L170-L173

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Ck.mono {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k l : ℕ) (hkl : k ≤ l)
    (f : M → ℂ) (hf : Ck n z l f) : Ck n z k f := by sorry
