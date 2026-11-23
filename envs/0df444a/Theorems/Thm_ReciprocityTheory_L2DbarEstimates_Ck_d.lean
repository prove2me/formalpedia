-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
-- name    : ReciprocityTheory.L2DbarEstimates.Ck.d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:09:28.125731+00:00
-- url     : https://prove2.me/theorems/02ef528a-d2fc-479f-828c-60e56537e6ac
-- title:
--   Ck: d
-- statement:
--   The Ck construction uses the d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L197-L200

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

theorem ReciprocityTheory.L2DbarEstimates.Ck.d {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (j : Fin n)
    (f : M → ℂ) (hf : Ck n z (k + 1) f) : Ck n z k (d n z j f) := by sorry
