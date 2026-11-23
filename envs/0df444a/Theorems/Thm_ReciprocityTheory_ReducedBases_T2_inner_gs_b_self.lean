-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_b_self
-- name    : ReciprocityTheory.ReducedBases.T2.inner_gs_b_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:05.11349+00:00
-- url     : https://prove2.me/theorems/73f42137-d95d-40f2-86d7-444baa511dd1
-- title:
--   T2: inner gs b self
-- statement:
--   The T2 construction uses the inner gs b self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L65-L68

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

theorem ReciprocityTheory.ReducedBases.T2.inner_gs_b_self (b : Fin d → E) (k : Fin d) : ⟪gs b k, b k⟫_ℝ = ‖gs b k‖ ^ 2 := by sorry
