-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ChA_Hf_add_left
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ChA.Hf_add_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:10.33382+00:00
-- url     : https://prove2.me/theorems/0bb21e3d-2ae2-5ded-a842-da55e522b4b5
-- title:
--   Ch A: Hf add left
-- statement:
--   The Ch A construction uses the Hf add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean#L24-L26

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

theorem ReciprocityTheory.ChartRestriction.G.I2.ChA.Hf_add_left {ι : Type} [Fintype ι] (v v' w : EuclideanSpace ℂ ι) :
    Hf (v + v') w = Hf v w + Hf v' w := by sorry
