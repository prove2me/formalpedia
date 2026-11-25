-- Prove2me | Theorems.Thm_PI_StabPairs_ConvAlg_rhoOf_mulVec_of_ker
-- name    : PI.StabPairs.ConvAlg.rhoOf_mulVec_of_ker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:11.598794+00:00
-- url     : https://prove2.me/theorems/6bd0cd92-53f8-4181-9bd4-f4c4031e554d
-- title:
--   Conv Alg: rho Of mul Vec of ker
-- statement:
--   The Conv Alg construction uses the rho Of mul Vec of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/ConvAlg.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/ConvAlg.lean#L20-L24

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

theorem PI.StabPairs.ConvAlg.rhoOf_mulVec_of_ker (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (v : n → ℂ) (hv : (Fᴴ * H) *ᵥ v = 0) : rhoOf H F W *ᵥ v = v := by sorry
