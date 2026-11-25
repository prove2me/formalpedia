-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_single
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Hf_single
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:30.58315+00:00
-- url     : https://prove2.me/theorems/ada10dd4-f56a-5d02-ab5f-5947c151cb4c
-- title:
--   I2: Hf single
-- statement:
--   The I2 construction uses the Hf single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormSqNonnegGaussianTorus.lean#L20-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormSqNonnegGaussianTorus.lean#L20-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus
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

theorem ReciprocityTheory.ChartRestriction.G.I2.Hf_single {ι : Type} [Fintype ι] [DecidableEq ι] (j j' : ι) :
    Hf (EuclideanSpace.single j (1 : ℂ)) (EuclideanSpace.single j' 1) = if j = j' then 1 else 0 := by sorry
