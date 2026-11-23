-- Prove2me | Theorems.Thm_PI_LocDualGen_FpU_repr_sum
-- name    : PI.LocDualGen.FpU.repr_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:33.942235+00:00
-- url     : https://prove2.me/theorems/54d38b57-cff8-4f88-b23f-71259b1a2556
-- title:
--   Fp U: repr sum
-- statement:
--   The Fp U construction uses the repr sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/IsClosedO.lean#L52-L54

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

theorem PI.LocDualGen.FpU.repr_sum {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (c : ι → R) (i : ι) : b.repr (∑ j, c j • b j) i = c i := by sorry
