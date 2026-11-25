-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_rt_map_inj
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.rt_map_inj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:29:18.40342+00:00
-- url     : https://prove2.me/theorems/d8cd3730-405c-5c83-a781-ff5c1ba4693c
-- title:
--   In HHClass Fin: rt map inj
-- statement:
--   The In HHClass Fin construction uses the rt map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean#L36-L39

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.rt_map_inj (I : Formalism.MainNotions.S.AutInst) {p q : Type} (M N : Matrix p q I.E)
    (h : M.map (rtι I) = N.map (rtι I)) : M = N := by sorry
