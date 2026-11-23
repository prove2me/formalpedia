-- Prove2me | Theorems.Thm_PI_OkpW_finite_quot
-- name    : PI.OkpW.finite_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:48.042344+00:00
-- url     : https://prove2.me/theorems/79b43928-efaa-4e52-bcdd-cc75e4dee6b3
-- title:
--   Okp W: finite quot
-- statement:
--   The Okp W construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L80-L81

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW
variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]

theorem PI.OkpW.finite_quot (hK : Module.finrank ℚ K = 2) : Finite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := by sorry
