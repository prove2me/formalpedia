-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_mulVec_idem
-- name    : ReciprocityTheory.L2DbarEstimates.projPerp_mulVec_idem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:18.852655+00:00
-- url     : https://prove2.me/theorems/7d10c9c2-6199-4ea9-be51-78735fd73b37
-- title:
--   L2 Dbar Estimates: proj Perp mul Vec idem
-- statement:
--   The L2 Dbar Estimates construction uses the proj Perp mul Vec idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L65-L68

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

theorem ReciprocityTheory.L2DbarEstimates.projPerp_mulVec_idem {g : Fin p → ℂ} (hg : g ≠ 0) (w : Fin p → ℂ) :
    projPerp g *ᵥ (projPerp g *ᵥ w) = projPerp g *ᵥ w := by sorry
