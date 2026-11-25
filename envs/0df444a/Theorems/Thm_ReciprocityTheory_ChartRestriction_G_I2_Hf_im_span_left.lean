-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_span_left
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Hf_im_span_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:09.193207+00:00
-- url     : https://prove2.me/theorems/d4b48fac-a947-47f5-b4a1-f633ea738d93
-- title:
--   I2: Hf im span left
-- statement:
--   The I2 construction uses the Hf im span left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean#L69-L76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
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
open scoped InnerProductSpace
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.Hf_im_span_left (S : Set (EuclideanSpace ℂ ι)) (w : EuclideanSpace ℂ ι)
    (h : ∀ v ∈ S, (Hf v w).im = 0) : ∀ v ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by sorry
