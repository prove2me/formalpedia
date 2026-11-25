-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ltLog_type
-- name    : ReciprocityTheory.ChartRestriction.L1.ltLog_type
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:45:55.644451+00:00
-- url     : https://prove2.me/theorems/d3c9d4f5-a038-4aaf-b5eb-21e4733a7a73
-- title:
--   L1: lt Log type
-- statement:
--   The L1 construction uses the lt Log type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgFinA.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgFinA.lean#L82-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgFinA
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

theorem ReciprocityTheory.ChartRestriction.L1.ltLog_type (hl : 2 ≤ l) (τ : K →+* K) : IsFunEqType l (l ^ 2) τ (ltLog K l) := by sorry
