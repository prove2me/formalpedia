-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_rt_inj
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.rt_inj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:31:53.147099+00:00
-- url     : https://prove2.me/theorems/9a909247-2fe9-41d0-9740-d5a0c348ea42
-- title:
--   In HHClass Fin: rt inj
-- statement:
--   The In HHClass Fin construction uses the rt inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean#L15-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean#L15-L34

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.rt_inj (I : Formalism.MainNotions.S.AutInst) : Function.Injective (rtι I) := by sorry
