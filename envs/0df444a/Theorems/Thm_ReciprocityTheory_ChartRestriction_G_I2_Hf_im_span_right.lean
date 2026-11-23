-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_span_right
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Hf_im_span_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:36.632403+00:00
-- url     : https://prove2.me/theorems/b10c3f00-d663-43b2-9b40-bbbe03a092a5
-- title:
--   I2: Hf im span right
-- statement:
--   The I2 construction uses the Hf im span right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitA.lean#L78-L85

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Hf_im_span_right (S : Set (EuclideanSpace ℂ ι)) (v : EuclideanSpace ℂ ι)
    (h : ∀ w ∈ S, (Hf v w).im = 0) : ∀ w ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by sorry
