-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ChA_prj_Mc
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ChA.prj_Mc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:05.547715+00:00
-- url     : https://prove2.me/theorems/de903ed4-c552-575a-80fe-ff5a3b31b6ee
-- title:
--   Ch A: prj Mc
-- statement:
--   The Ch A construction uses the prj Mc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean#L93-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean#L93-L97

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.ChA

theorem ReciprocityTheory.ChartRestriction.G.I2.ChA.prj_Mc {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) :
    prj σ (Mc σ c v) = c • prj σ v := by sorry
