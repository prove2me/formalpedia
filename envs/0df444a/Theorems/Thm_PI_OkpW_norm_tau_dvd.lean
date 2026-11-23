-- Prove2me | Theorems.Thm_PI_OkpW_norm_tau_dvd
-- name    : PI.OkpW.norm_tau_dvd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:46.679751+00:00
-- url     : https://prove2.me/theorems/be30c59f-24bd-4449-8f99-f60361adecd2
-- title:
--   Okp W: norm tau dvd
-- statement:
--   The Okp W construction uses the norm tau dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L57-L62

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

theorem PI.OkpW.norm_tau_dvd (τ : K →+* ℂ_[p]) {a : 𝓞 K} {k : ℕ} (h : (p : 𝓞 K) ^ k ∣ a) :
    ‖τ (a : K)‖ ≤ (p : ℝ)⁻¹ ^ k := by sorry
