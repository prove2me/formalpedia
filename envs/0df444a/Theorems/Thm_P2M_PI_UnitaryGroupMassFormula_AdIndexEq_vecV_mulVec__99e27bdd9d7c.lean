-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_AdIndexEq_vecV_mulVec__99e27bdd9d7c
-- name    : P2M_PI_UnitaryGroupMassFormula_AdIndexEq_vecV_mulVec__99e27bdd9d7c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:40.27425+00:00
-- url     : https://prove2.me/theorems/112d6ec4-f18a-4c58-85de-9da794c1584d
-- title:
--   P2 M PI Unitary Group Mass Formula Ad Index Eq vec V mul Vec  99e27bdd9d7c: P2 M PI Unitary Group Mass Formula Ad Index Eq vec V mul Vec  99e27bdd9d7c
-- statement:
--   The P2 M PI Unitary Group Mass Formula Ad Index Eq vec V mul Vec  99e27bdd9d7c construction uses the P2 M PI Unitary Group Mass Formula Ad Index Eq vec V mul Vec  99e27bdd9d7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/CompactLocalGlobal.lean#L113-L117

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

theorem P2M_PI_UnitaryGroupMassFormula_AdIndexEq_vecV_mulVec__99e27bdd9d7c (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (x : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (M *ᵥ x) = M.map (PI.FinKW.psiV I v).toRingHom *ᵥ PI.FinKW.vecV I v x := by sorry

alias «PI».«UnitaryGroupMassFormula».«AdIndexEq».«vecV_mulVec'» := P2M_PI_UnitaryGroupMassFormula_AdIndexEq_vecV_mulVec__99e27bdd9d7c
