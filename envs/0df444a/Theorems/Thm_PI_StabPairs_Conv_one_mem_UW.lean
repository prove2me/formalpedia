-- Prove2me | Theorems.Thm_PI_StabPairs_Conv_one_mem_UW
-- name    : PI.StabPairs.Conv.one_mem_UW
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:39:18.228256+00:00
-- url     : https://prove2.me/theorems/7e286031-1bc8-4fdf-b705-a312cd739f46
-- title:
--   Conv: one mem UW
-- statement:
--   The Conv construction uses the one mem UW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/ConverseStepOf.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/ConverseStepOf.lean#L11-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStepOf
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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem PI.StabPairs.Conv.one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by sorry
