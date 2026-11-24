-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ltLog_const
-- name    : ReciprocityTheory.ChartRestriction.L1.ltLog_const
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:44:44.959875+00:00
-- url     : https://prove2.me/theorems/95244fc7-61d1-4e4b-864d-fbdb9d4d3036
-- title:
--   L1: lt Log const
-- statement:
--   The L1 construction uses the lt Log const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L102-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L102-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
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
variable {K : Type} [Field K] (g2 g3 : K)

theorem ReciprocityTheory.ChartRestriction.L1.ltLog_const (l : ℕ) (hl : 2 ≤ l) : constantCoeff (ltLog K l) = 0 := by sorry
