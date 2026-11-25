-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_hform_J__8f64264f3f82
-- name    : P2M_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_hform_J__8f64264f3f82
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:03:40.849429+00:00
-- url     : https://prove2.me/theorems/4593ab31-707d-5a3a-9e53-1b7fee54a799
-- title:
--   P2 M PI Unitary Group Mass Formula In HHClass Fin Frame hform J  8f64264f3f82: P2 M PI Unitary Group Mass Formula In HHClass Fin Frame hform J  8f64264f3f82
-- statement:
--   The P2 M PI Unitary Group Mass Formula In HHClass Fin Frame hform J  8f64264f3f82 construction uses the P2 M PI Unitary Group Mass Formula In HHClass Fin Frame hform J  8f64264f3f82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L148-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L148-L154

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

theorem P2M_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_hform_J__8f64264f3f82 (fr : Frame I S) (x y : Fin fr.k → I.E) :
    hform (starRingEnd I.E) fr.J' x y =
      hform (starRingEnd I.E) I.J (fr.B *ᵥ Sum.elim 0 x) (fr.B *ᵥ Sum.elim 0 y) := by sorry

alias «PI».«UnitaryGroupMassFormula».«InHHClassFin».«Frame».«hform_J'» := P2M_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_hform_J__8f64264f3f82
