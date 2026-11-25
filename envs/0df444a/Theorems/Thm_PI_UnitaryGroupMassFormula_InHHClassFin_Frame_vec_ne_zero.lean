-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_Frame_vec_ne_zero
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.Frame.vec_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:05:22.605862+00:00
-- url     : https://prove2.me/theorems/0dc0a5c6-ad7f-4871-a2a1-2be18361575b
-- title:
--   Frame: vec ne zero
-- statement:
--   The Frame construction uses the vec ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L166-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L166-L175

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.Frame.vec_ne_zero (fr : Frame I S) (x : Fin fr.k → I.E) (hx : x ≠ 0) :
    fr.B *ᵥ Sum.elim 0 x ≠ 0 := by sorry
