-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_add_right
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.hform_add_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:12:55.826664+00:00
-- url     : https://prove2.me/theorems/79ace422-fcb0-4931-af21-36789c52bd94
-- title:
--   In HHClass Fin: hform add right
-- statement:
--   The In HHClass Fin construction uses the hform add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L32-L34

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y y' : n → A) : hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by sorry
