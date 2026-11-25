-- Prove2me | Theorems.Thm_PI_LocDualGen_FpD_tr_alg_mul
-- name    : PI.LocDualGen.FpD.tr_alg_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:26.733622+00:00
-- url     : https://prove2.me/theorems/2265c725-13b8-59ce-8712-ac639ade288b
-- title:
--   Fp D: tr alg mul
-- statement:
--   The Fp D construction uses the tr alg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/FpDual.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/FpDual.lean#L19-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel
open PI PI.LocDualGen PI.LocDualGen.FpD
open PI.LocDualGen.W
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]

theorem PI.LocDualGen.FpD.tr_alg_mul (q : ℚ_[l]) (z : K) :
    Algebra.trace ℚ_[l] K (algebraMap ℚ_[l] K q * z) = q * Algebra.trace ℚ_[l] K z := by sorry
