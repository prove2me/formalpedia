-- Prove2me | Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_ModW_MG_val_mul__7724171e7634
-- name    : P2M_PI_QuotSetU_UnitaryGroupMassFormula_ModW_MG_val_mul__7724171e7634
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:22.053482+00:00
-- url     : https://prove2.me/theorems/b8333fec-9241-4d6d-ab56-718ff9926f9b
-- title:
--   P2 M PI Quot Set U Unitary Group Mass Formula Mod W MG val mul  7724171e7634: P2 M PI Quot Set U Unitary Group Mass Formula Mod W MG val mul  7724171e7634
-- statement:
--   The P2 M PI Quot Set U Unitary Group Mass Formula Mod W MG val mul  7724171e7634 construction uses the P2 M PI Quot Set U Unitary Group Mass Formula Mod W MG val mul  7724171e7634 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModBase.lean#L73-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/ModBase.lean#L73-L73

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
open PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG

theorem P2M_PI_QuotSetU_UnitaryGroupMassFormula_ModW_MG_val_mul__7724171e7634 (x y : MG G hG) : (x * y).val = rmulQ y.toM x.val := by sorry

alias «PI».«QuotSetU».«UnitaryGroupMassFormula».«ModW».«MG».«val_mul'» := P2M_PI_QuotSetU_UnitaryGroupMassFormula_ModW_MG_val_mul__7724171e7634
