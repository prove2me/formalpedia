-- Prove2me | Theorems.Thm_PI_OkpW_tau_sub
-- name    : PI.OkpW.tau_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:18.886129+00:00
-- url     : https://prove2.me/theorems/b9a547d1-a6f5-4c1b-8eef-014a5d8f4d07
-- title:
--   Okp W: tau sub
-- statement:
--   The Okp W construction uses the tau sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L52-L53

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

theorem PI.OkpW.tau_sub (τ : K →+* ℂ_[p]) (x y : 𝓞 K) : τ ((x - y : 𝓞 K) : K) = τ (x : K) - τ (y : K) := by sorry
