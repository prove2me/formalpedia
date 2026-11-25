-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uMat_term
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uMat_term
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:02.758796+00:00
-- url     : https://prove2.me/theorems/ddabd2b4-e221-4311-8e20-160ca7fde8df
-- title:
--   Frame Degree Data: u Mat term
-- statement:
--   The Frame Degree Data construction uses the u Mat term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UMatUpper.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UMatUpper.lean#L30-L39

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uMat_term (G : Matrix (Fin n) (Fin n) ℂ) (c m j : Fin n) :
    uMat G j c * G j m = (if j = c then G c m else 0) +
      (if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ * G j m else 0) := by sorry
