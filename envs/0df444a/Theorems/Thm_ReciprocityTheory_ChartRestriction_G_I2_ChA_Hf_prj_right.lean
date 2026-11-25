-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ChA_Hf_prj_right
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ChA.Hf_prj_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:24.962212+00:00
-- url     : https://prove2.me/theorems/9f66ecb2-6166-485b-a040-813d5088cc07
-- title:
--   Ch A: Hf prj right
-- statement:
--   The Ch A construction uses the Hf prj right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean#L46-L53

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

theorem ReciprocityTheory.ChartRestriction.G.I2.ChA.Hf_prj_right {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {v : Vsp dim} (hv : InPart σ v) (x : Vsp dim) :
    Hf v (prj σ x) = Hf v x := by sorry
