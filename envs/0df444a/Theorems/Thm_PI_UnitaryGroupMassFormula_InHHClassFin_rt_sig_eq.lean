-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_rt_sig_eq
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.rt_sig_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:11:43.656249+00:00
-- url     : https://prove2.me/theorems/c9e76415-ea69-5075-bee2-d8c13c5d98a1
-- title:
--   In HHClass Fin: rt sig eq
-- statement:
--   The In HHClass Fin construction uses the rt sig eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean#L70-L73

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_RtUnitaryOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin

theorem PI.UnitaryGroupMassFormula.InHHClassFin.rt_sig_eq (I : Formalism.MainNotions.S.AutInst) : (I.cm.sig : I.E →+* I.E) = starRingEnd I.E := by sorry
