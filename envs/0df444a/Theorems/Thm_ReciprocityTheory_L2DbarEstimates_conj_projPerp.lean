-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_conj_projPerp
-- name    : ReciprocityTheory.L2DbarEstimates.conj_projPerp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:13.818342+00:00
-- url     : https://prove2.me/theorems/511de309-8ee3-5e6c-9bc0-ee1f633982a8
-- title:
--   L2 Dbar Estimates: conj proj Perp
-- statement:
--   The L2 Dbar Estimates construction uses the conj proj Perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L70-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean#L70-L80

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

theorem ReciprocityTheory.L2DbarEstimates.conj_projPerp (g : Fin p → ℂ) (i l : Fin p) :
    conj (projPerp g i l) = projPerp g l i := by sorry
