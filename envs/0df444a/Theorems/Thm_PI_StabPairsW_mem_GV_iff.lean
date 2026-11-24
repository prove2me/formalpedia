-- Prove2me | Theorems.Thm_PI_StabPairsW_mem_GV_iff
-- name    : PI.StabPairsW.mem_GV_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:28:56.332861+00:00
-- url     : https://prove2.me/theorems/f3684349-0a0a-4ae4-b828-e27144d66740
-- title:
--   Stab Pairs W: mem GV iff
-- statement:
--   The Stab Pairs W construction uses the mem GV iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L79-L79

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

theorem PI.StabPairsW.mem_GV_iff {g : B.Mat k r} : g ∈ B.GV k r ↔ gᴴ * Hpk k r * g = Hpk k r := by sorry
