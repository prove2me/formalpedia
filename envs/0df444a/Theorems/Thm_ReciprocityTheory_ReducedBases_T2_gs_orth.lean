-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_orth
-- name    : ReciprocityTheory.ReducedBases.T2.gs_orth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:15.651252+00:00
-- url     : https://prove2.me/theorems/507c457f-2a6a-4a73-852e-1bf1dabb51e6
-- title:
--   T2: gs orth
-- statement:
--   The T2 construction uses the gs orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L20-L21

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

theorem ReciprocityTheory.ReducedBases.T2.gs_orth (b : Fin d → E) {i j : Fin d} (h : i ≠ j) : ⟪gs b i, gs b j⟫_ℝ = 0 := by sorry
