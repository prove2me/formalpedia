-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_FPw_gaussianInner_jet__df00fb8a6479
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_FPw_gaussianInner_jet__df00fb8a6479
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:17:22.749993+00:00
-- url     : https://prove2.me/theorems/0f3ca85d-38f1-44b6-adc0-9138a3f00eec
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 FPw gaussian Inner jet  df00fb8a6479: P2 M Reciprocity Theory Chart Restriction G I2 FPw gaussian Inner jet  df00fb8a6479
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 FPw gaussian Inner jet  df00fb8a6479 construction uses the P2 M Reciprocity Theory Chart Restriction G I2 FPw gaussian Inner jet  df00fb8a6479 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/ExpNEllMem.lean#L172-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/ExpNEllMem.lean#L172-L194

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaIPZeroRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex Filter Topology
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_FPw_gaussianInner_jet__df00fb8a6479 {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    paIP q (paU q a F) G = paIP q (paJet c (paU q a F)) G := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«FPw».«gaussianInner_jet'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_FPw_gaussianInner_jet__df00fb8a6479
