-- Prove2me | Theorems.Thm_PI_StabPairsW_herm_self_re
-- name    : PI.StabPairsW.herm_self_re
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:28:59.331902+00:00
-- url     : https://prove2.me/theorems/a77fe6fd-4c36-4bdb-9cb4-172937ef922b
-- title:
--   Stab Pairs W: herm self re
-- statement:
--   The Stab Pairs W construction uses the herm self re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L258-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L258-L261

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

theorem PI.StabPairsW.herm_self_re (v : Fin (2 * r + k + 1) → ℂ) :
    ((herm (Hpk k r) v v).re : ℂ) = herm (Hpk k r) v v := by sorry
