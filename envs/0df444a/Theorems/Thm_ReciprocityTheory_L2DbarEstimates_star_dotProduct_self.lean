-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_star_dotProduct_self
-- name    : ReciprocityTheory.L2DbarEstimates.star_dotProduct_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:50.171803+00:00
-- url     : https://prove2.me/theorems/b42f9463-1866-4caf-828a-684707028ed4
-- title:
--   L2 Dbar Estimates: star dot Product self
-- statement:
--   The L2 Dbar Estimates construction uses the star dot Product self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L35-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.star_dotProduct_self (g : Fin p → ℂ) : star g ⬝ᵥ g = ((sqNorm g : ℝ) : ℂ) := by sorry
