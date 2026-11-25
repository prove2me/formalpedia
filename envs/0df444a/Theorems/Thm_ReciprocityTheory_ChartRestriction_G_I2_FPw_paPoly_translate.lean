-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paPoly_translate
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.paPoly_translate
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:49.084313+00:00
-- url     : https://prove2.me/theorems/dd5f8dd4-0878-541b-b080-287ce4e555ad
-- title:
--   FPw: pa Poly translate
-- statement:
--   The FPw construction uses the pa Poly translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaPolyTranslate.lean#L182-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaPolyTranslate.lean#L182-L203

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.paPoly_translate {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (a : EuclideanSpace ℂ ι) : (fun v => F (v - a)) ∈ paPoly c := by sorry
