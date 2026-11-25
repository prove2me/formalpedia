-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_col_entry
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.inst_col_entry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:41:35.67512+00:00
-- url     : https://prove2.me/theorems/9c486a4c-2f11-53e3-8f80-6e98622955ec
-- title:
--   Unitary Group Mass Formula: inst col entry
-- statement:
--   The Unitary Group Mass Formula construction uses the inst col entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstPlace.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstPlace.lean#L39-L42

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

theorem PI.ScMuExists.UnitaryGroupMassFormula.inst_col_entry {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hm : m *ᵥ Pi.single i 1 = Pi.single i 1) (r : Fin n) : m r i = if r = i then 1 else 0 := by sorry
