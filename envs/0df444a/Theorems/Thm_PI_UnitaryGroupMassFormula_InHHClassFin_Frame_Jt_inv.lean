-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_Jt_inv
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.Frame.Jt_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:41:45.373902+00:00
-- url     : https://prove2.me/theorems/8757516d-be79-42c1-8efb-c622a6a5042e
-- title:
--   Frame: Jt inv
-- statement:
--   The Frame construction uses the Jt inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L100-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L100-L116

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.Frame.Jt_inv (fr : Frame I S) :
    fr.Jt * (fr.Bi * I.J⁻¹ * cT (starRingEnd I.E) fr.Bi) = 1 := by sorry
