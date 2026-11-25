-- Prove2me | Theorems.Thm_PI_LocDualGen_FpU_Phi_add
-- name    : PI.LocDualGen.FpU.Phi_add
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:42.347669+00:00
-- url     : https://prove2.me/theorems/cf17e5c9-f7d1-4bd8-a573-48624e25476b
-- title:
--   Fp U: Phi add
-- statement:
--   The Fp U construction uses the Phi add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L91-L94

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

theorem PI.LocDualGen.FpU.Phi_add (hcont : Continuous (algebraMap ℚ_[l] K)) (c c' : Fin (fdim K l) → ℤ_[l]) (s : ℤ_[l]) :
    Phi K l hcont (c + s • c') = Phi K l hcont c + iotaR K l hcont s * Phi K l hcont c' := by sorry
