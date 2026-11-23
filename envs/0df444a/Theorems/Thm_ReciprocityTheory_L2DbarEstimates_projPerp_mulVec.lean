-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_mulVec
-- name    : ReciprocityTheory.L2DbarEstimates.projPerp_mulVec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:29.990565+00:00
-- url     : https://prove2.me/theorems/4735dfc0-77f3-4d56-afcc-b3a87fae1ddf
-- title:
--   L2 Dbar Estimates: proj Perp mul Vec
-- statement:
--   The L2 Dbar Estimates construction uses the proj Perp mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L45-L56

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

theorem ReciprocityTheory.L2DbarEstimates.projPerp_mulVec (g w : Fin p → ℂ) :
    projPerp g *ᵥ w = w - (((sqNorm g : ℝ) : ℂ)⁻¹ * (star g ⬝ᵥ w)) • g := by sorry
