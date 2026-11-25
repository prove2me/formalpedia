-- Prove2me | Theorems.Thm_PI_EF_logDeriv_local
-- name    : PI.EF.logDeriv_local
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:08.232606+00:00
-- url     : https://prove2.me/theorems/a4a306d1-41e6-5f16-a309-abf1927a9d8e
-- title:
--   EF: log Deriv local
-- statement:
--   The EF construction uses the log Deriv local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructA.lean#L9-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructA.lean#L9-L34

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

theorem PI.EF.logDeriv_local {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hfin : analyticOrderAt f ρ ≠ ⊤) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, f s ≠ 0 ∧
      logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + k s := by sorry
