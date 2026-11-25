-- Prove2me | Theorems.Thm_PI_LocDualGen_EpF_differentIdeal_eq_top
-- name    : PI.LocDualGen.EpF.differentIdeal_eq_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:38.852063+00:00
-- url     : https://prove2.me/theorems/d9143e28-e920-5952-86c1-915963b0302c
-- title:
--   Ep F: different Ideal eq top
-- statement:
--   The Ep F construction uses the different Ideal eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualField.lean#L44-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualField.lean#L44-L146

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open ValuativeRel IsDedekindDomain
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
open PI PI.LocDualGen PI.LocDualGen.EpF
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CharZero K]
local notation "C" => integralClosure 𝒪[K] L
attribute [local instance] dd fr mf tfC
attribute [local instance] sepFR

theorem PI.LocDualGen.EpF.differentIdeal_eq_top
    (hU : ∀ x : C, x * x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] →
      x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) :
    differentIdeal 𝒪[K] C = ⊤ := by sorry
