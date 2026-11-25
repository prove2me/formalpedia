-- Prove2me | Theorems.Thm_PI_LocDualGen_EpF_selfDual_field
-- name    : PI.LocDualGen.EpF.selfDual_field
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:59.223664+00:00
-- url     : https://prove2.me/theorems/a2ce2a71-3b08-4abe-9865-611dae124b5d
-- title:
--   Ep F: self Dual field
-- statement:
--   The Ep F construction uses the self Dual field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualField.lean#L156-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualField.lean#L156-L170

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

theorem PI.LocDualGen.EpF.selfDual_field
    (hU : ∀ x : C, x * x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] →
      x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) (x : L) :
    (∀ y ∈ C, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ C := by sorry
