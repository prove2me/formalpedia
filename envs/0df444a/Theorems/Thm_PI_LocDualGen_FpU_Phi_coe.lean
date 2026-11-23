-- Prove2me | Theorems.Thm_PI_LocDualGen_FpU_Phi_coe
-- name    : PI.LocDualGen.FpU.Phi_coe
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:02.928325+00:00
-- url     : https://prove2.me/theorems/19129865-e754-4f54-950d-1ccfded1c1fa
-- title:
--   Fp U: Phi coe
-- statement:
--   The Fp U construction uses the Phi coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L85-L89

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

theorem PI.LocDualGen.FpU.Phi_coe (hcont : Continuous (algebraMap ℚ_[l] K)) (c : Fin (fdim K l) → ℤ_[l]) :
    ((Phi K l hcont c : 𝒪[K]) : K) = ∑ i, algebraMap ℚ_[l] K (c i : ℚ_[l]) * (blift K l i : K) := by sorry
