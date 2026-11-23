-- Prove2me | Theorems.Thm_PI_OkpW_norm_p_cp
-- name    : PI.OkpW.norm_p_cp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:36.072252+00:00
-- url     : https://prove2.me/theorems/80e80316-78de-4f0d-a864-a1d652e21436
-- title:
--   Okp W: norm p cp
-- statement:
--   The Okp W construction uses the norm p cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertPrimeTeichmuller/NormLeOneOfIntegralInt.lean#L41-L43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW
variable {p : ℕ} [hp : Fact p.Prime]

theorem PI.OkpW.norm_p_cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by sorry
