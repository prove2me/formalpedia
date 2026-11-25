-- Prove2me | Theorems.Thm_PI_StabSplit_Proj_prj_star
-- name    : PI.StabSplit.Proj.prj_star
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:04.778684+00:00
-- url     : https://prove2.me/theorems/96f454e5-08fb-5ebd-949b-6ceb3468b1d5
-- title:
--   Proj: prj star
-- statement:
--   The Proj construction uses the prj star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L29-L31

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

theorem PI.StabSplit.Proj.prj_star (hH : Hᴴ = H) : (prj H Y)ᴴ * H = H * prj H Y := by sorry
