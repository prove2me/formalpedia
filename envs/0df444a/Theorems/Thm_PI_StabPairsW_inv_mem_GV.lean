-- Prove2me | Theorems.Thm_PI_StabPairsW_inv_mem_GV
-- name    : PI.StabPairsW.inv_mem_GV
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:28:28.459807+00:00
-- url     : https://prove2.me/theorems/cf974e15-0b20-4a88-a081-601568145906
-- title:
--   Stab Pairs W: inv mem GV
-- statement:
--   The Stab Pairs W construction uses the inv mem GV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L97-L106

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

theorem PI.StabPairsW.inv_mem_GV {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ ∈ B.GV k r := by sorry
