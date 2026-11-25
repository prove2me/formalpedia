-- Prove2me | Theorems.Thm_PI_OkpW_exists_inv_mod
-- name    : PI.OkpW.exists_inv_mod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:28.294619+00:00
-- url     : https://prove2.me/theorems/e1cc6272-f81b-464f-bca2-856ea94d997a
-- title:
--   Okp W: exists inv mod
-- statement:
--   The Okp W construction uses the exists inv mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L94-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L94-L102

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

theorem PI.OkpW.exists_inv_mod (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K} (ha : ¬ (p : 𝓞 K) ∣ a) :
    ∃ b : 𝓞 K, (p : 𝓞 K) ∣ a * b - 1 := by sorry
