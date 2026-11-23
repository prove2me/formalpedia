-- Prove2me | Theorems.Thm_PI_OkpW_teich_spec
-- name    : PI.OkpW.teich_spec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:31.472366+00:00
-- url     : https://prove2.me/theorems/e567ca77-36aa-4a74-9c19-6f8cdc2920ce
-- title:
--   Okp W: teich spec
-- statement:
--   The Okp W construction uses the teich spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L68-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFrob
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_DvdPowQSub
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

theorem PI.OkpW.teich_spec (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a : 𝓞 K) :
    Tendsto (tseq τ a) atTop (𝓝 (teich τ a)) ∧
      ∀ k, ‖teich τ a - tseq τ a k‖ ≤ (p : ℝ)⁻¹ ^ (k + 1) := by sorry
