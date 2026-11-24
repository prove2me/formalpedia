-- Prove2me | Theorems.Thm_PI_StabPairsW_det_Zhat_ne
-- name    : PI.StabPairsW.det_Zhat_ne
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:28:46.878127+00:00
-- url     : https://prove2.me/theorems/0f487cf9-f70d-46b2-b60c-97097bb698f1
-- title:
--   Stab Pairs W: det Zhat ne
-- statement:
--   The Stab Pairs W construction uses the det Zhat ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L287-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L287-L304

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
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
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}

theorem PI.StabPairsW.det_Zhat_ne (z z' : Fin (2 * r + k + 1) → ℂ) (hS : Std k r z z') (γ : B.Mat k r) (hP : PosPt k r z z' γ) :
    (Zhat k r z z' γ).det ≠ 0 := by sorry
