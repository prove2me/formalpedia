-- Prove2me | Theorems.Thm_PI_StabPairsW_isUnit_det_of_mem_GV
-- name    : PI.StabPairsW.isUnit_det_of_mem_GV
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:28:43.431161+00:00
-- url     : https://prove2.me/theorems/ab6ed4ee-aed9-4f3c-bb32-6da53a8a6533
-- title:
--   Stab Pairs W: is Unit det of mem GV
-- statement:
--   The Stab Pairs W construction uses the is Unit det of mem GV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L94-L95

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

theorem PI.StabPairsW.isUnit_det_of_mem_GV {g : B.Mat k r} (hg : g ∈ B.GV k r) : IsUnit g.det := by sorry
