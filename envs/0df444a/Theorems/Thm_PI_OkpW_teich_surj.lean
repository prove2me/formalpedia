-- Prove2me | Theorems.Thm_PI_OkpW_teich_surj
-- name    : PI.OkpW.teich_surj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:53.120849+00:00
-- url     : https://prove2.me/theorems/f59655bb-dfac-577c-82c1-d94398231293
-- title:
--   Okp W: teich surj
-- statement:
--   The Okp W construction uses the teich surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/TeichNeZero.lean#L73-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/TeichNeZero.lean#L73-L112

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_DvdPowQSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_TeichNeZero
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
variable (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b)
include hq

theorem PI.OkpW.teich_surj (hK : Module.finrank ℚ K = 2) (τ : K →+* ℂ_[p])
    (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {ζ : ℂ_[p]} (hζ : ζ ^ (p ^ 2 - 1) = 1) :
    ∃ a : 𝓞 K, teich τ a = ζ := by sorry
