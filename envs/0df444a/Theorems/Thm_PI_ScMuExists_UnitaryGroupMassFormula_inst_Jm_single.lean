-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_Jm_single
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.inst_Jm_single
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:37:47.853802+00:00
-- url     : https://prove2.me/theorems/0cd5650d-ef6b-4069-a0fa-f43ce920c285
-- title:
--   Unitary Group Mass Formula: inst Jm single
-- statement:
--   The Unitary Group Mass Formula construction uses the inst Jm single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstPlace.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstPlace.lean#L17-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula

theorem PI.ScMuExists.UnitaryGroupMassFormula.inst_Jm_single {n : ℕ} (ε : Fin n → Bool) (i : Fin n) :
    Formalism.REAL.Jm ε *ᵥ Pi.single i 1 = (if ε i then (1 : ℂ) else -1) • Pi.single i 1 := by sorry
