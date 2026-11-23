-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_Lm_diag
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:57.946264+00:00
-- url     : https://prove2.me/theorems/b52f4f4f-4fbb-4f04-b836-d58ad323559e
-- title:
--   LUPf: Lm diag
-- statement:
--   The LUPf construction uses the Lm diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfA.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfA.lean#L52-L53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_diag (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Lm M i i = 1 := by sorry
