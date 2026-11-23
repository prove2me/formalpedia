-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_sum_smul_b
-- name    : ReciprocityTheory.ReducedBases.T2.sum_smul_b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:59.525807+00:00
-- url     : https://prove2.me/theorems/7e99eefc-f0ff-4850-a225-92501496c2cc
-- title:
--   T2: sum smul b
-- statement:
--   The T2 construction uses the sum smul b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L118-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L118-L128

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

theorem ReciprocityTheory.ReducedBases.T2.sum_smul_b (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) :
    ∑ l, c l • b l = ∑ j, nu b c j • gs b j := by sorry
