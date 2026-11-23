-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_ne_zero
-- name    : ReciprocityTheory.ReducedBases.T2.gs_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:05.625809+00:00
-- url     : https://prove2.me/theorems/6797ef11-6706-48b6-8d74-edbe41ded1bf
-- title:
--   T2: gs ne zero
-- statement:
--   The T2 construction uses the gs ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/GsInnerBOfLt.lean#L70-L71

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

theorem ReciprocityTheory.ReducedBases.T2.gs_ne_zero (b : Fin d → E) (hb : LinearIndependent ℝ b) (k : Fin d) : gs b k ≠ 0 := by sorry
