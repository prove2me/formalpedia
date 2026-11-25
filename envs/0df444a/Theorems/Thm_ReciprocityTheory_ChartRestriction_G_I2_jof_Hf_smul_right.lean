-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_jof_Hf_smul_right
-- name    : ReciprocityTheory.ChartRestriction.G.I2.jof_Hf_smul_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:31:12.573583+00:00
-- url     : https://prove2.me/theorems/edc32375-d7fe-53ef-9a0f-8aa4cdc80eb0
-- title:
--   I2: jof Hf smul right
-- statement:
--   The I2 construction uses the jof Hf smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormSqNonnegGaussianTorus.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/L2NormSqNonnegGaussianTorus.lean#L10-L13

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

theorem ReciprocityTheory.ChartRestriction.G.I2.jof_Hf_smul_right {ι : Type} [Fintype ι] (x u : EuclideanSpace ℂ ι) (c : ℂ) :
    Hf x (c • u) = (starRingEnd ℂ) c * Hf x u := by sorry
