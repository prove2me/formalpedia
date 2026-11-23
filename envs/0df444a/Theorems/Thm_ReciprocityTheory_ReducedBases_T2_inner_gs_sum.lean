-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_sum
-- name    : ReciprocityTheory.ReducedBases.T2.inner_gs_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:57.813412+00:00
-- url     : https://prove2.me/theorems/b80d6182-c308-47e1-88f2-6cda92e0d80d
-- title:
--   T2: inner gs sum
-- statement:
--   The T2 construction uses the inner gs sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L130-L132

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

theorem ReciprocityTheory.ReducedBases.T2.inner_gs_sum (b : Fin d → E) (x : Fin d → ℝ) (j : Fin d) :
    ⟪gs b j, ∑ k, x k • gs b k⟫_ℝ = x j * ‖gs b j‖ ^ 2 := by sorry
