-- Prove2me | Theorems.Thm_PI_StabSplit_Proj_prj_Y
-- name    : PI.StabSplit.Proj.prj_Y
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:52.706491+00:00
-- url     : https://prove2.me/theorems/f2945c0f-700d-4c4c-ba7a-14c3b7c2dbf5
-- title:
--   Proj: prj Y
-- statement:
--   The Proj construction uses the prj Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L15-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabSplit PI.StabSplit.Proj
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
variable (H : Matrix n n ℂ) (Y : Matrix n ι ℂ)

theorem PI.StabSplit.Proj.prj_Y (hG : IsUnit (Yᴴ * H * Y).det) : prj H Y * Y = Y := by sorry
