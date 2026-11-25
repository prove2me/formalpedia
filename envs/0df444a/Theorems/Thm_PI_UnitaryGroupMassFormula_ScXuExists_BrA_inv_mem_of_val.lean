-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_inv_mem_of_val
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.BrA.inv_mem_of_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:40:47.837149+00:00
-- url     : https://prove2.me/theorems/552d8559-99ba-4e34-a1e6-d7142b965a28
-- title:
--   Br A: inv mem of val
-- statement:
--   The Br A construction uses the inv mem of val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LocalDataSatisfyLinearHypotheses.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LocalDataSatisfyLinearHypotheses.lean#L11-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocalDataSatisfyLinearHypotheses
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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem PI.UnitaryGroupMassFormula.ScXuExists.BrA.inv_mem_of_val (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : ℕ)
    (hc : Valued.v ((c : v.adicCompletion I.F)) = 1) : ((c : KV I v))⁻¹ ∈ OV I v := by sorry
