-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_ScXuExists_vecV_smul__5475ffa01793
-- name    : P2M_PI_UnitaryGroupMassFormula_ScXuExists_vecV_smul__5475ffa01793
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:30:46.33884+00:00
-- url     : https://prove2.me/theorems/83cf5953-b408-47b7-bf41-cdeb877527fa
-- title:
--   P2 M PI Unitary Group Mass Formula Sc Xu Exists vec V smul  5475ffa01793: P2 M PI Unitary Group Mass Formula Sc Xu Exists vec V smul  5475ffa01793
-- statement:
--   The P2 M PI Unitary Group Mass Formula Sc Xu Exists vec V smul  5475ffa01793 construction uses the P2 M PI Unitary Group Mass Formula Sc Xu Exists vec V smul  5475ffa01793 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/ValNatCastLtOne.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/ValNatCastLtOne.lean#L48-L52

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

theorem P2M_PI_UnitaryGroupMassFormula_ScXuExists_vecV_smul__5475ffa01793 (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (a : I.E ⊗[I.F] Af I.F)
    (x : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (a • x) = PI.FinKW.psiV I v a • PI.FinKW.vecV I v x := by sorry

alias «PI».«UnitaryGroupMassFormula».«ScXuExists».«vecV_smul'» := P2M_PI_UnitaryGroupMassFormula_ScXuExists_vecV_smul__5475ffa01793
