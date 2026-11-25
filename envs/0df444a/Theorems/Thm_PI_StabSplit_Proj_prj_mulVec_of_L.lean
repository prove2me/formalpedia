-- Prove2me | Theorems.Thm_PI_StabSplit_Proj_prj_mulVec_of_L
-- name    : PI.StabSplit.Proj.prj_mulVec_of_L
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:12.615797+00:00
-- url     : https://prove2.me/theorems/18d3760c-58ef-4f6e-904a-18ba56013503
-- title:
--   Proj: prj mul Vec of L
-- statement:
--   The Proj construction uses the prj mul Vec of L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L36-L37

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

theorem PI.StabSplit.Proj.prj_mulVec_of_L {v : n → ℂ} (hv : (Yᴴ * H) *ᵥ v = 0) : prj H Y *ᵥ v = 0 := by sorry
