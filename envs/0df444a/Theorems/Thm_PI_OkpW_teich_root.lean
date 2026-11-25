-- Prove2me | Theorems.Thm_PI_OkpW_teich_root
-- name    : PI.OkpW.teich_root
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:36.37775+00:00
-- url     : https://prove2.me/theorems/238a53cc-8571-4798-b057-ac4e1ec37888
-- title:
--   Okp W: teich root
-- statement:
--   The Okp W construction uses the teich root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/TeichNeZero.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/TeichNeZero.lean#L50-L57

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

theorem PI.OkpW.teich_root (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K}
    (ha : ¬ (p : 𝓞 K) ∣ a) : teich τ a ^ (p ^ 2 - 1) = 1 := by sorry
