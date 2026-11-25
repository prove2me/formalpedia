-- Prove2me | Theorems.Thm_PI_LocDualGen_FpU_iotaR_coe
-- name    : PI.LocDualGen.FpU.iotaR_coe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:39.436624+00:00
-- url     : https://prove2.me/theorems/d841b526-6ae8-4944-aeb3-28c6e8089aac
-- title:
--   Fp U: iota R coe
-- statement:
--   The Fp U construction uses the iota R coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L44-L45

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

theorem PI.LocDualGen.FpU.iotaR_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (a : ℤ_[l]) :
    ((iotaR K l hcont a : 𝒪[K]) : K) = algebraMap ℚ_[l] K (a : ℚ_[l]) := by sorry
