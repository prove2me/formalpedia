-- Prove2me | Theorems.Thm_PI_OkpW_tseq_step
-- name    : PI.OkpW.tseq_step
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:48.76141+00:00
-- url     : https://prove2.me/theorems/2115f750-122f-5c96-a82d-7772bbcbd0e3
-- title:
--   Okp W: tseq step
-- statement:
--   The Okp W construction uses the tseq step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L61-L66

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

theorem PI.OkpW.tseq_step (τ : K →+* ℂ_[p]) (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b) (a : 𝓞 K)
    (k : ℕ) : ‖tseq τ a (k + 1) - tseq τ a k‖ ≤ (p : ℝ)⁻¹ ^ (k + 1) := by sorry
