-- Prove2me | Theorems.Thm_PI_OkpW_tau_pow
-- name    : PI.OkpW.tau_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:14.993572+00:00
-- url     : https://prove2.me/theorems/0958244b-9743-4145-85e4-9075d75f8fae
-- title:
--   Okp W: tau pow
-- statement:
--   The Okp W construction uses the tau pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L49-L50

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

theorem PI.OkpW.tau_pow (τ : K →+* ℂ_[p]) (x : 𝓞 K) (n : ℕ) : τ ((x ^ n : 𝓞 K) : K) = τ (x : K) ^ n := by sorry
