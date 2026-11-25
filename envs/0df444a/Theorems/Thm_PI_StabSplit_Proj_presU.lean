-- Prove2me | Theorems.Thm_PI_StabSplit_Proj_presU
-- name    : PI.StabSplit.Proj.presU
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:18.041745+00:00
-- url     : https://prove2.me/theorems/015df36d-e3db-4a6b-9844-1bf7825583e6
-- title:
--   Proj: pres U
-- statement:
--   The Proj construction uses the pres U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L50-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/PrjMulVecOfL.lean#L50-L64

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

theorem PI.StabSplit.Proj.presU (hG : IsUnit (Yᴴ * H * Y).det) (g : Matrix n n ℂ) (hg : gᴴ * H * g = H)
    (hdet : IsUnit g.det) (C : Matrix ι ι ℂ) (hC : g⁻¹ * Y = Y * C) :
    prj H Y * g * (1 - prj H Y) = 0 := by sorry
