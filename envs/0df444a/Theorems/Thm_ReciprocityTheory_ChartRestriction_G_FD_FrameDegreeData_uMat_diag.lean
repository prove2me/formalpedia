-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uMat_diag
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uMat_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:10.024666+00:00
-- url     : https://prove2.me/theorems/a97c8bdb-c90b-4457-a90b-e1defdf8630b
-- title:
--   Frame Degree Data: u Mat diag
-- statement:
--   The Frame Degree Data construction uses the u Mat diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UMatUpper.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UMatUpper.lean#L21-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uMat_diag (G : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : uMat G j j = 1 := by sorry
