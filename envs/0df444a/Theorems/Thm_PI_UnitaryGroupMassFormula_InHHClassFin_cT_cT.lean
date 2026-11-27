-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_cT_cT
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.cT_cT
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:56:23.635127+00:00
-- url     : https://prove2.me/theorems/97ff2f50-ca1e-5099-8a7d-ab97c451cdf0
-- title:
--   In HHClass Fin: c T c T
-- statement:
--   The In HHClass Fin construction uses the c T c T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/HformSumRight.lean#L92-L94

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.cT_cT (M : Matrix (Fin I.n) (Fin I.n) I.E) : cT (starRingEnd I.E) (cT (starRingEnd I.E) M) = M := by sorry
