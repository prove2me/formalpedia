-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_b_sub_gs_mem
-- name    : ReciprocityTheory.ReducedBases.T2.b_sub_gs_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:01.935616+00:00
-- url     : https://prove2.me/theorems/1bb4183d-1d83-45ed-9da2-1d163e1fb3f8
-- title:
--   T2: b sub gs mem
-- statement:
--   The T2 construction uses the b sub gs mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L23-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L23-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem ReciprocityTheory.ReducedBases.T2.b_sub_gs_mem (b : Fin d → E) (k : Fin d) : b k - gs b k ∈ span ℝ (b '' Set.Iio k) := by sorry
