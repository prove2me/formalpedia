-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_span
-- name    : ReciprocityTheory.ReducedBases.T2.inner_gs_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:38.077535+00:00
-- url     : https://prove2.me/theorems/3a6e8cb4-6007-4337-a089-5d707d26583b
-- title:
--   T2: inner gs span
-- statement:
--   The T2 construction uses the inner gs span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L38-L46

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

theorem ReciprocityTheory.ReducedBases.T2.inner_gs_span (b : Fin d → E) (k : Fin d) {y : E} (hy : y ∈ span ℝ (b '' Set.Iio k)) :
    ⟪gs b k, y⟫_ℝ = 0 := by sorry
