-- Prove2me | Theorems.Thm_PI_StabPairs_ConvAlg_rhoOf_unitary
-- name    : PI.StabPairs.ConvAlg.rhoOf_unitary
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:00.627891+00:00
-- url     : https://prove2.me/theorems/24dabf5e-4243-5d18-ac9f-222e5d2cc3ac
-- title:
--   Conv Alg: rho Of unitary
-- statement:
--   The Conv Alg construction uses the rho Of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/ConvAlg.lean#L26-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/ConvAlg.lean#L26-L65

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

theorem PI.StabPairs.ConvAlg.rhoOf_unitary (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (hH : Hᴴ = H) (hG : IsUnit (Fᴴ * H * F).det) (hW : Wᴴ * (Fᴴ * H * F) * W = Fᴴ * H * F) :
    (rhoOf H F W)ᴴ * H * rhoOf H F W = H := by sorry
