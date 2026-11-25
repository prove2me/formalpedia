-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_gaussianInner_jet
-- name    : ReciprocityTheory.ChartRestriction.G.I2.gaussianInner_jet
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:45.999189+00:00
-- url     : https://prove2.me/theorems/54258700-b301-57b3-abb0-5802b1eaad95
-- title:
--   I2: gaussian Inner jet
-- statement:
--   The I2 construction uses the gaussian Inner jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L203-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L203-L206

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

theorem ReciprocityTheory.ChartRestriction.G.I2.gaussianInner_jet {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    paIP q (paU q a F) G = paIP q (paJet c (paU q a F)) G := by sorry
