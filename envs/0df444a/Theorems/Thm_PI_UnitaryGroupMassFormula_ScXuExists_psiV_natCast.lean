-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_psiV_natCast
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.psiV_natCast
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:30:50.234847+00:00
-- url     : https://prove2.me/theorems/30827a93-902c-4204-96bb-020ad3d3148c
-- title:
--   Sc Xu Exists: psi V nat Cast
-- statement:
--   The Sc Xu Exists construction uses the psi V nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/ValNatCastLtOne.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/ValNatCastLtOne.lean#L59-L60

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

theorem PI.UnitaryGroupMassFormula.ScXuExists.psiV_natCast (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) :
    PI.FinKW.psiV I v (m : I.E ⊗[I.F] Af I.F) = (m : RV I v) := by sorry
