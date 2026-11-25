-- Prove2me | Theorems.Thm_PI_StabSplit_Proj_Y_inj
-- name    : PI.StabSplit.Proj.Y_inj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:01.451514+00:00
-- url     : https://prove2.me/theorems/d1717640-a86e-40e6-bc7d-b62ec7490cbd
-- title:
--   Proj: Y inj
-- statement:
--   The Proj construction uses the Y inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L77-L80

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

theorem PI.StabSplit.Proj.Y_inj (hG : IsUnit (Yᴴ * H * Y).det) (c : ι → ℂ) (hc : Y *ᵥ c = 0) : c = 0 := by sorry
