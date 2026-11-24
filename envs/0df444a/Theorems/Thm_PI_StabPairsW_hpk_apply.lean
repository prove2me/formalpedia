-- Prove2me | Theorems.Thm_PI_StabPairsW_hpk_apply
-- name    : PI.StabPairsW.hpk_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:28:54.099946+00:00
-- url     : https://prove2.me/theorems/80840542-313a-433a-ae13-1b423c3af9ad
-- title:
--   Stab Pairs W: hpk apply
-- statement:
--   The Stab Pairs W construction uses the hpk apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/IsUnitDetOfMemGV.lean#L16-L21

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

theorem PI.StabPairsW.hpk_apply (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l.val = sgI k r i.val then (if i.val = r + k then -1 else 1) else 0 := by sorry
