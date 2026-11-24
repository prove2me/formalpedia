-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_J__eq_dcb540cc7f1c
-- name    : P2M_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_J__eq_dcb540cc7f1c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:11:19.780675+00:00
-- url     : https://prove2.me/theorems/053304ad-c8e6-4d9f-bbd5-f62fcb72da86
-- title:
--   P2 M PI Unitary Group Mass Formula In HHClass Fin Frame J  eq dcb540cc7f1c: P2 M PI Unitary Group Mass Formula In HHClass Fin Frame J  eq dcb540cc7f1c
-- statement:
--   The P2 M PI Unitary Group Mass Formula In HHClass Fin Frame J  eq dcb540cc7f1c construction uses the P2 M PI Unitary Group Mass Formula In HHClass Fin Frame J  eq dcb540cc7f1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L17-L17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}

theorem P2M_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_J__eq_dcb540cc7f1c (fr : Frame I S) : fr.J' = fr.Jt.toBlocks₂₂ := by sorry

alias «PI».«UnitaryGroupMassFormula».«InHHClassFin».«Frame».«J'_eq» := P2M_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_J__eq_dcb540cc7f1c
