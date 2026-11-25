-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_natCast_tmul
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.natCast_tmul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:49:02.807452+00:00
-- url     : https://prove2.me/theorems/e16c6dfe-43f5-5c0b-9812-a349d462ceb3
-- title:
--   Sc Xu Exists: nat Cast tmul
-- statement:
--   The Sc Xu Exists construction uses the nat Cast tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/NatCastTmul.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/NatCastTmul.lean#L35-L39

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
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

theorem PI.UnitaryGroupMassFormula.ScXuExists.natCast_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) :
    ((m : KV I v) ⊗ₜ[I.F] (1 : I.E)) = (m : RV I v) := by sorry
