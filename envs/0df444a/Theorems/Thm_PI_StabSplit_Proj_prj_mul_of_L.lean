-- Prove2me | Theorems.Thm_PI_StabSplit_Proj_prj_mul_of_L
-- name    : PI.StabSplit.Proj.prj_mul_of_L
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:36:57.276816+00:00
-- url     : https://prove2.me/theorems/10f07eeb-f764-503e-a7e7-107ca43daf15
-- title:
--   Proj: prj mul of L
-- statement:
--   The Proj construction uses the prj mul of L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L39-L41

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

theorem PI.StabSplit.Proj.prj_mul_of_L {m : Type*} [Fintype m] (A : Matrix n m ℂ) (hA : (Yᴴ * H) * A = 0) :
    prj H Y * A = 0 := by sorry
