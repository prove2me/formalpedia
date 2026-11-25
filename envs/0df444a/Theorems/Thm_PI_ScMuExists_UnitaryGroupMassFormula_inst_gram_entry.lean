-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_gram_entry
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.inst_gram_entry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:50.940614+00:00
-- url     : https://prove2.me/theorems/87c4e00c-4982-5858-8645-00eeecfac2d5
-- title:
--   Unitary Group Mass Formula: inst gram entry
-- statement:
--   The Unitary Group Mass Formula construction uses the inst gram entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstAdapt.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstAdapt.lean#L10-L12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAdapt
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

theorem PI.ScMuExists.UnitaryGroupMassFormula.inst_gram_entry {n : ℕ} (X J Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Xᴴ * J * Y) a b = ∑ s, ∑ r, star (X r a) * J r s * Y s b := by sorry
