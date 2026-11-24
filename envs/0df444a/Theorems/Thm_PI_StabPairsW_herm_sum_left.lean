-- Prove2me | Theorems.Thm_PI_StabPairsW_herm_sum_left
-- name    : PI.StabPairsW.herm_sum_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:28:14.906009+00:00
-- url     : https://prove2.me/theorems/e5d2bd32-2bf2-4044-a0e5-66b634571adf
-- title:
--   Stab Pairs W: herm sum left
-- statement:
--   The Stab Pairs W construction uses the herm sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L203-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L203-L208

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

theorem PI.StabPairsW.herm_sum_left (v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ a, c a • v a) w = ∑ a, c a * herm (Hpk k r) (v a) w := by sorry
