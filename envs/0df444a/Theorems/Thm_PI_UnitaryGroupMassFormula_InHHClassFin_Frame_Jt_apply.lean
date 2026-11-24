-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_Jt_apply
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.Frame.Jt_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:13:02.155851+00:00
-- url     : https://prove2.me/theorems/d5102a75-3c2d-452a-b3bf-286fb3f1ff16
-- title:
--   Frame: Jt apply
-- statement:
--   The Frame construction uses the Jt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L70-L74

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.Frame.Jt_apply (fr : Frame I S) (p q : Fin fr.m ⊕ Fin fr.k) :
    fr.Jt p q = hform (starRingEnd I.E) I.J (fun a => fr.B a p) (fun a => fr.B a q) := by sorry
