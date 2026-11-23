-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uMat_upper
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uMat_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:22.799399+00:00
-- url     : https://prove2.me/theorems/0c956b80-b4ea-4b6e-83f3-725f1d42b32f
-- title:
--   Frame Degree Data: u Mat upper
-- statement:
--   The Frame Degree Data construction uses the u Mat upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UMatUpper.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UMatUpper.lean#L24-L28

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uMat_upper (G : Matrix (Fin n) (Fin n) ℂ) : (uMat G).BlockTriangular id := by sorry
