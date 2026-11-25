-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_comb
-- name    : ReciprocityTheory.ReducedBases.T2.inner_gs_comb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:11.352804+00:00
-- url     : https://prove2.me/theorems/e2b9a314-baab-4dda-b443-f37c4f70125f
-- title:
--   T2: inner gs comb
-- statement:
--   The T2 construction uses the inner gs comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L134-L136

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

theorem ReciprocityTheory.ReducedBases.T2.inner_gs_comb (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) (j : Fin d) :
    ⟪gs b j, ∑ l, c l • b l⟫_ℝ = nu b c j * ‖gs b j‖ ^ 2 := by sorry
