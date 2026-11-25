-- Prove2me | Theorems.Thm_PI_StabPairs_ConvAlg_rhoOf_mul
-- name    : PI.StabPairs.ConvAlg.rhoOf_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:27:16.654812+00:00
-- url     : https://prove2.me/theorems/19aa3a99-a361-45e9-aa1a-a2efcbfbd2c7
-- title:
--   Conv Alg: rho Of mul
-- statement:
--   The Conv Alg construction uses the rho Of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/ConvAlg.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/ConvAlg.lean#L13-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg
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
open PI PI.StabPairs PI.StabPairs.ConvAlg
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem PI.StabPairs.ConvAlg.rhoOf_mul (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (hG : IsUnit (Fᴴ * H * F).det) : rhoOf H F W * F = F * W := by sorry
