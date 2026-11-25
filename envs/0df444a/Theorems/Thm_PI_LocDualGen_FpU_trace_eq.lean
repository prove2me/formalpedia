-- Prove2me | Theorems.Thm_PI_LocDualGen_FpU_trace_eq
-- name    : PI.LocDualGen.FpU.trace_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:27:24.459234+00:00
-- url     : https://prove2.me/theorems/28859f6c-7b50-4691-9a12-0cfec143588d
-- title:
--   Fp U: trace eq
-- statement:
--   The Fp U construction uses the trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/UnramifiedDualGenerator.lean#L120-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/UnramifiedDualGenerator.lean#L120-L130

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator
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

theorem PI.LocDualGen.FpU.trace_eq (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : Algebra.trace ℚ_[l] K (x : K) =
      ((∑ i, coef K l hcont huni (x * blift K l i) i : ℤ_[l]) : ℚ_[l]) := by sorry
