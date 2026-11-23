-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_apply
-- name    : ReciprocityTheory.L2DbarEstimates.projPerp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:01.505941+00:00
-- url     : https://prove2.me/theorems/20328461-307d-469c-aacb-ac408f5fab9e
-- title:
--   L2 Dbar Estimates: proj Perp apply
-- statement:
--   The L2 Dbar Estimates construction uses the proj Perp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L41-L43

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

theorem ReciprocityTheory.L2DbarEstimates.projPerp_apply (g : Fin p → ℂ) (i l : Fin p) :
    projPerp g i l = (if i = l then 1 else 0) - ((sqNorm g : ℝ) : ℂ)⁻¹ * (g i * conj (g l)) := by sorry
