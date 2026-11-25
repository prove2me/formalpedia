-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_ScXuExists_BrA_vecV_incl__c4acc129ac4b
-- name    : P2M_PI_UnitaryGroupMassFormula_ScXuExists_BrA_vecV_incl__c4acc129ac4b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:03:55.782823+00:00
-- url     : https://prove2.me/theorems/b3f05f42-653c-5f17-9266-e55beb7ec9c0
-- title:
--   P2 M PI Unitary Group Mass Formula Sc Xu Exists Br A vec V incl  c4acc129ac4b: P2 M PI Unitary Group Mass Formula Sc Xu Exists Br A vec V incl  c4acc129ac4b
-- statement:
--   The P2 M PI Unitary Group Mass Formula Sc Xu Exists Br A vec V incl  c4acc129ac4b construction uses the P2 M PI Unitary Group Mass Formula Sc Xu Exists Br A vec V incl  c4acc129ac4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondCoordinateVectorMemSpan.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondCoordinateVectorMemSpan.lean#L91-L95

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem P2M_PI_UnitaryGroupMassFormula_ScXuExists_BrA_vecV_incl__c4acc129ac4b (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (l : Fin I.n → I.E) :
    PI.FinKW.vecV I v (incl I l) = Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l := by sorry

alias «PI».«UnitaryGroupMassFormula».«ScXuExists».«BrA».«vecV_incl'» := P2M_PI_UnitaryGroupMassFormula_ScXuExists_BrA_vecV_incl__c4acc129ac4b
