-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_matV_coe
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.matV_coe
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:50.516255+00:00
-- url     : https://prove2.me/theorems/cb9c7378-f868-484c-a8c5-940a823da2a0
-- title:
--   Ad Index Eq: mat V coe
-- statement:
--   The Ad Index Eq construction uses the mat V coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L15-L18

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.matV_coe (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ((matV I v g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)).map (PI.FinKW.psiV I v).toRingHom := by sorry
