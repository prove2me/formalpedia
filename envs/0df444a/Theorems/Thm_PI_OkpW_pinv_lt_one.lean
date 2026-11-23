-- Prove2me | Theorems.Thm_PI_OkpW_pinv_lt_one
-- name    : PI.OkpW.pinv_lt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:04.165459+00:00
-- url     : https://prove2.me/theorems/ab5ea972-d645-4877-bdd1-17b2b16d5666
-- title:
--   Okp W: pinv lt one
-- statement:
--   The Okp W construction uses the pinv lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/DvdPowQSub.lean#L39-L40

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

theorem PI.OkpW.pinv_lt_one : (p : ℝ)⁻¹ < 1 := by sorry
