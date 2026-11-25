-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_InHHClassFin_cT_mul__58967eadcc89
-- name    : P2M_PI_UnitaryGroupMassFormula_InHHClassFin_cT_mul__58967eadcc89
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:04:31.512794+00:00
-- url     : https://prove2.me/theorems/c63ea4ae-5907-589c-9c1f-50321f8aee82
-- title:
--   P2 M PI Unitary Group Mass Formula In HHClass Fin c T mul  58967eadcc89: P2 M PI Unitary Group Mass Formula In HHClass Fin c T mul  58967eadcc89
-- statement:
--   The P2 M PI Unitary Group Mass Formula In HHClass Fin c T mul  58967eadcc89 construction uses the P2 M PI Unitary Group Mass Formula In HHClass Fin c T mul  58967eadcc89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L96-L98

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

theorem P2M_PI_UnitaryGroupMassFormula_InHHClassFin_cT_mul__58967eadcc89 {m p q : Type} [Fintype p] (M : Matrix m p I.E) (N : Matrix p q I.E) :
    cT (starRingEnd I.E) (M * N) = cT (starRingEnd I.E) N * cT (starRingEnd I.E) M := by sorry

alias «PI».«UnitaryGroupMassFormula».«InHHClassFin».«cT_mul'» := P2M_PI_UnitaryGroupMassFormula_InHHClassFin_cT_mul__58967eadcc89
