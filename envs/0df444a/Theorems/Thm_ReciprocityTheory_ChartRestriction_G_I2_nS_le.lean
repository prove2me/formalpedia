-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nS_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nS_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:46.029845+00:00
-- url     : https://prove2.me/theorems/92274be0-4f7b-4b6d-a2fd-ece26b14c849
-- title:
--   I2: n S le
-- statement:
--   The I2 construction uses the n S le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVB.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVB.lean#L46-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}

theorem ReciprocityTheory.ChartRestriction.G.I2.nS_le [IsTotallyComplex E] (ξ : Vsp dim) (σ : E →+* ℂ) : nS ξ σ ≤ ‖ξ‖ ^ 2 := by sorry
