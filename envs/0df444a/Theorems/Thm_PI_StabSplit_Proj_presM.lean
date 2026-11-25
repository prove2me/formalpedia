-- Prove2me | Theorems.Thm_PI_StabSplit_Proj_presM
-- name    : PI.StabSplit.Proj.presM
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:16.629638+00:00
-- url     : https://prove2.me/theorems/6120a2b8-58bf-4071-bde4-4036c003fccd
-- title:
--   Proj: pres M
-- statement:
--   The Proj construction uses the pres M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L43-L48

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

theorem PI.StabSplit.Proj.presM (hG : IsUnit (Yᴴ * H * Y).det) (g : Matrix n n ℂ) (C : Matrix ι ι ℂ) (hC : g * Y = Y * C) :
    (1 - prj H Y) * g * prj H Y = 0 := by sorry
