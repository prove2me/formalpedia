-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_gaussianInner_jet_eq_sum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.gaussianInner_jet_eq_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:24.112985+00:00
-- url     : https://prove2.me/theorems/436f1728-d67c-4908-95e5-a498552486c8
-- title:
--   I2: gaussian Inner jet eq sum
-- statement:
--   The I2 construction uses the gaussian Inner jet eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L272-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L272-L275

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.gaussianInner_jet_eq_sum {q c : ℕ} (hq : 1 ≤ q) (H : EuclideanSpace ℂ ι → ℂ) {G : EuclideanSpace ℂ ι → ℂ}
    (hG : G ∈ paPoly c) :
    paIP q (paJet c H) G = ∑ α ∈ paS c, (paD α H / paFact α) * paIP q (paMono α) G := by sorry
