-- Prove2me | Theorems.Thm_PI_EF_exists_regular_part
-- name    : PI.EF.exists_regular_part
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:39.451273+00:00
-- url     : https://prove2.me/theorems/8362793c-bd68-442b-8a6d-91d27ca048e3
-- title:
--   EF: exists regular part
-- statement:
--   The EF construction uses the exists regular part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructA.lean#L36-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructA.lean#L36-L93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set

theorem PI.EF.exists_regular_part {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K) (Z : Finset ℂ)
    (hZ0 : ∀ ρ ∈ Z, f ρ = 0) (hK : ∀ s ∈ K, f s = 0 → s ∈ Z)
    (hfin : ∀ ρ ∈ K, analyticOrderAt f ρ ≠ ⊤) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H K ∧ ∀ s ∈ K, f s ≠ 0 →
      logDeriv f s = H s + ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) := by sorry
