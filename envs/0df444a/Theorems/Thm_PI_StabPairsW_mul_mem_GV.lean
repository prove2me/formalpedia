-- Prove2me | Theorems.Thm_PI_StabPairsW_mul_mem_GV
-- name    : PI.StabPairsW.mul_mem_GV
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:04.659878+00:00
-- url     : https://prove2.me/theorems/88a1e407-4671-4bb4-83d9-aa1dc2649684
-- title:
--   Stab Pairs W: mul mem GV
-- statement:
--   The Stab Pairs W construction uses the mul mem GV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L81-L86

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

theorem PI.StabPairsW.mul_mem_GV {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) : a * b ∈ B.GV k r := by sorry
