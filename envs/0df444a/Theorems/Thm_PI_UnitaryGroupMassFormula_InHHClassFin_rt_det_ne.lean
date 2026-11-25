-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_rt_det_ne
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.rt_det_ne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:50.341053+00:00
-- url     : https://prove2.me/theorems/4c21296e-820b-5651-b2ba-6ba95102fc5f
-- title:
--   In HHClass Fin: rt det ne
-- statement:
--   The In HHClass Fin construction uses the rt det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean#L60-L68

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.rt_det_ne (I : Formalism.MainNotions.S.AutInst) {k : Type} [Fintype k] [DecidableEq k]
    (M : Matrix k k I.E) (u : GL k (rtA I)) (hu : (u : Matrix k k (rtA I)) = M.map (rtι I)) :
    M.det ≠ 0 := by sorry
