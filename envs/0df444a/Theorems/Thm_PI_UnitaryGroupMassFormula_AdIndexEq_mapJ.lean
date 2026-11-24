-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_mapJ
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.mapJ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:16:45.079823+00:00
-- url     : https://prove2.me/theorems/f4e8dd94-eab2-4757-af6a-e593f636ce10
-- title:
--   Ad Index Eq: map J
-- statement:
--   The Ad Index Eq construction uses the map J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L79-L84

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem PI.UnitaryGroupMassFormula.AdIndexEq.mapJ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (PI.FinKW.psiV I v).toRingHom =
      I.J.map (inclV I v) := by sorry
