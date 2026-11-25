-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_rt_uMat
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:43:36.078216+00:00
-- url     : https://prove2.me/theorems/604afaa5-9c1e-4302-b92b-b49ef6d4ee70
-- title:
--   In HHClass Fin: rt u Mat
-- statement:
--   The In HHClass Fin construction uses the rt u Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/RtUnitaryOf.lean#L123-L126

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.rt_uMat (I : Formalism.MainNotions.S.AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ UJ (starRingEnd I.E) I.J)
    (v : InfinitePlace I.F) :
    Formalism.MainNotions.S.uMat (rtReal I γ hγ v) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by sorry
