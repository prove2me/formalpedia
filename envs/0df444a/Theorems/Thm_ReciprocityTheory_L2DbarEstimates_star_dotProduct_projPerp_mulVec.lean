-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_star_dotProduct_projPerp_mulVec
-- name    : ReciprocityTheory.L2DbarEstimates.star_dotProduct_projPerp_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:48.775384+00:00
-- url     : https://prove2.me/theorems/9e62b7f9-9438-4ab5-8725-c8be7923ab0c
-- title:
--   L2 Dbar Estimates: star dot Product proj Perp mul Vec
-- statement:
--   The L2 Dbar Estimates construction uses the star dot Product proj Perp mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L58-L63

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

theorem ReciprocityTheory.L2DbarEstimates.star_dotProduct_projPerp_mulVec {g : Fin p → ℂ} (hg : g ≠ 0) (w : Fin p → ℂ) :
    star g ⬝ᵥ (projPerp g *ᵥ w) = 0 := by sorry
