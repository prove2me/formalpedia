-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_partialYAtZero
-- name    : ReciprocityTheory.ChartRestriction.L1.integralPS_partialYAtZero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:00.403295+00:00
-- url     : https://prove2.me/theorems/a17ad0e9-4c9b-48cc-a7a6-e03bd8e976fb
-- title:
--   L1: integral PS partial YAt Zero
-- statement:
--   The L1 construction uses the integral PS partial YAt Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L117-L122

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K}

theorem ReciprocityTheory.ChartRestriction.L1.integralPS_partialYAtZero (hΦ : IntegralMv Φ) : IntegralPS (d2 Φ) := by sorry
