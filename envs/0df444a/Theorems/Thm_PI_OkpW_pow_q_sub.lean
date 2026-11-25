-- Prove2me | Theorems.Thm_PI_OkpW_pow_q_sub
-- name    : PI.OkpW.pow_q_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:05.256892+00:00
-- url     : https://prove2.me/theorems/bc38f2a8-e6e4-521f-9e3a-31ff95153e14
-- title:
--   Okp W: pow q sub
-- statement:
--   The Okp W construction uses the pow q sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L83-L92

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

theorem PI.OkpW.pow_q_sub (hK : Module.finrank ℚ K = 2) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime)
    (a : 𝓞 K) (n : ℕ) : (p : 𝓞 K) ∣ a ^ ((p ^ 2) ^ n) - a := by sorry
