-- Prove2me | Theorems.Thm_PI_LocDualGen_FpU_res_iotaR
-- name    : PI.LocDualGen.FpU.res_iotaR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:36.685606+00:00
-- url     : https://prove2.me/theorems/8259ddfb-3a26-4546-a137-d903d9a0aaf2
-- title:
--   Fp U: res iota R
-- statement:
--   The Fp U construction uses the res iota R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L64-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing
open PI PI.LocDualGen PI.LocDualGen.FpU
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
variable [CharP 𝓀[K] l]
attribute [local instance] algRes

theorem PI.LocDualGen.FpU.res_iotaR (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    residue 𝒪[K] (iotaR K l hcont a) = algebraMap (ZMod l) 𝓀[K] (PadicInt.toZMod a) := by sorry
