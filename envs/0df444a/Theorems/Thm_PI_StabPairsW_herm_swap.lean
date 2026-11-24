-- Prove2me | Theorems.Thm_PI_StabPairsW_herm_swap
-- name    : PI.StabPairsW.herm_swap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:29:12.454734+00:00
-- url     : https://prove2.me/theorems/71013c8a-510c-40b6-aec1-20c1a4ae3dfb
-- title:
--   Stab Pairs W: herm swap
-- statement:
--   The Stab Pairs W construction uses the herm swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L150-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L150-L153

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

theorem PI.StabPairsW.herm_swap (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by sorry
