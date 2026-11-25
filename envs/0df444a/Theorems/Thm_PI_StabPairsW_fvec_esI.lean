-- Prove2me | Theorems.Thm_PI_StabPairsW_fvec_esI
-- name    : PI.StabPairsW.fvec_esI
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:23.90106+00:00
-- url     : https://prove2.me/theorems/4fb4dd7f-852a-4ca8-97fb-3b00199c0006
-- title:
--   Stab Pairs W: fvec es I
-- statement:
--   The Stab Pairs W construction uses the fvec es I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L224-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L224-L233

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

theorem PI.StabPairsW.fvec_esI (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : Fin (r + 1)) (a : Fin r) :
    fvec k r z c (esI k r a) = 0 := by sorry
