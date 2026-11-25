-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_ScXuExists_vecV_add__ede578f826c6
-- name    : P2M_PI_UnitaryGroupMassFormula_ScXuExists_vecV_add__ede578f826c6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:04:08.591089+00:00
-- url     : https://prove2.me/theorems/ed17e4f9-aa57-5270-9d18-f49b19eb6295
-- title:
--   P2 M PI Unitary Group Mass Formula Sc Xu Exists vec V add  ede578f826c6: P2 M PI Unitary Group Mass Formula Sc Xu Exists vec V add  ede578f826c6
-- statement:
--   The P2 M PI Unitary Group Mass Formula Sc Xu Exists vec V add  ede578f826c6 construction uses the P2 M PI Unitary Group Mass Formula Sc Xu Exists vec V add  ede578f826c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/ValNatCastLtOne.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/ValNatCastLtOne.lean#L54-L57

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem P2M_PI_UnitaryGroupMassFormula_ScXuExists_vecV_add__ede578f826c6 (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (x + y) = PI.FinKW.vecV I v x + PI.FinKW.vecV I v y := by sorry

alias «PI».«UnitaryGroupMassFormula».«ScXuExists».«vecV_add'» := P2M_PI_UnitaryGroupMassFormula_ScXuExists_vecV_add__ede578f826c6
