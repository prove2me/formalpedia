-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_inner_b_of_lt
-- name    : ReciprocityTheory.ReducedBases.T2.gs_inner_b_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:30.576861+00:00
-- url     : https://prove2.me/theorems/e02e17b9-757e-4608-b7b8-9d7bcf09b17f
-- title:
--   T2: gs inner b of lt
-- statement:
--   The T2 construction uses the gs inner b of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L17-L18

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

theorem ReciprocityTheory.ReducedBases.T2.gs_inner_b_of_lt (b : Fin d → E) {i j : Fin d} (h : i < j) : ⟪gs b j, b i⟫_ℝ = 0 := by sorry
