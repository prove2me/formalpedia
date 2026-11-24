-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_psiV_inclE
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.psiV_inclE
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:50:34.218794+00:00
-- url     : https://prove2.me/theorems/f5e456de-3d69-4592-b02c-a89e3d41cec1
-- title:
--   Ad Index Eq: psi V incl E
-- statement:
--   The Ad Index Eq construction uses the psi V incl E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L69-L71

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Theorems.Thm_PI_FinKW_LocTo_psiV_inclE

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.psiV_inclE (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    PI.FinKW.psiV I v (Formalism.UG.inclE (F := I.F) (Af I.F) e) = inclV I v e := by sorry
