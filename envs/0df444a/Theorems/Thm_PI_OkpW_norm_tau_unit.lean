-- Prove2me | Theorems.Thm_PI_OkpW_norm_tau_unit
-- name    : PI.OkpW.norm_tau_unit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:40.391264+00:00
-- url     : https://prove2.me/theorems/98711553-19f4-48d7-b204-809b47ae99ea
-- title:
--   Okp W: norm tau unit
-- statement:
--   The Okp W construction uses the norm tau unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/TeichNeZero.lean#L12-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/TeichNeZero.lean#L12-L31

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

theorem PI.OkpW.norm_tau_unit (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K}
    (ha : ¬ (p : 𝓞 K) ∣ a) : ‖τ (a : K)‖ = 1 := by sorry
