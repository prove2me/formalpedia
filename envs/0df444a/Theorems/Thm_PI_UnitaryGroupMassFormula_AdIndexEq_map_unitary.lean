-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_map_unitary
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.map_unitary
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:58.56929+00:00
-- url     : https://prove2.me/theorems/2a113dbc-7395-5e9d-a071-e3bde0b2f10c
-- title:
--   Ad Index Eq: map unitary
-- statement:
--   The Ad Index Eq construction uses the map unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L86-L94

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.map_unitary (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) M * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * M).map
              (PI.FinKW.psiV I v).toRingHom =
      Formalism.UG.cT (sigV I v) (M.map (PI.FinKW.psiV I v).toRingHom) * I.J.map (inclV I v) *
        M.map (PI.FinKW.psiV I v).toRingHom := by sorry
