-- Prove2me | Theorems.Thm_PI_StabPairsW_det_ne_of_mem_GV
-- name    : PI.StabPairsW.det_ne_of_mem_GV
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:44.66838+00:00
-- url     : https://prove2.me/theorems/86a9d156-699f-4492-8648-2dd1df91c757
-- title:
--   Stab Pairs W: det ne of mem GV
-- statement:
--   The Stab Pairs W construction uses the det ne of mem GV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L88-L92

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

theorem PI.StabPairsW.det_ne_of_mem_GV {g : B.Mat k r} (hg : g ∈ B.GV k r) : g.det ≠ 0 := by sorry
