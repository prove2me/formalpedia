-- Prove2me | Theorems.Thm_PI_OkpW_approx
-- name    : PI.OkpW.approx
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:14:34.383466+00:00
-- url     : https://prove2.me/theorems/e9144591-6c87-5c5e-b275-d9a3e6517926
-- title:
--   Okp W: approx
-- statement:
--   The Okp W construction uses the approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/UltrametricPairEstimate.lean#L41-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/UltrametricPairEstimate.lean#L41-L97

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_TeichNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_UltrametricPairEstimate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
noncomputable section
open PI PI.OkpW
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

theorem PI.OkpW.approx (τ : K →+* ℂ_[p]) (cO : 𝓞 K →+* 𝓞 K)
    (hqn : ∀ (a : 𝓞 K) (n : ℕ), (p : 𝓞 K) ∣ a ^ ((p ^ 2) ^ n) - a)
    (hfrob : ∀ a : 𝓞 K, (p : 𝓞 K) ∣ cO a - a ^ p) (n : ℕ) (a : 𝓞 K) :
    ∃ r ∈ Subring.closure (gens p), ‖τ (a : K) - r.1‖ ≤ (p : ℝ)⁻¹ ^ n ∧
      ‖τ ((cO a : 𝓞 K) : K) - r.2‖ ≤ (p : ℝ)⁻¹ ^ n := by sorry
