-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_norm_actT_sq
-- name    : ReciprocityTheory.ChartRestriction.G.I2.norm_actT_sq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:42.505809+00:00
-- url     : https://prove2.me/theorems/bf267d9c-28a3-4a1a-b510-0cc988b2fcc3
-- title:
--   I2: norm act T sq
-- statement:
--   The I2 construction uses the norm act T sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVB.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVB.lean#L112-L118

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

theorem ReciprocityTheory.ChartRestriction.G.I2.norm_actT_sq (t : (E →+* ℂ) → ℂ) (v : Vsp dim) :
    ‖actT t v‖ ^ 2 = ∑ σ, ‖t σ‖ ^ 2 * pN v σ := by sorry
