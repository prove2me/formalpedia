-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_norm_uc_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.norm_uc_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:49.465846+00:00
-- url     : https://prove2.me/theorems/f2bcb028-79fb-44c6-9d08-32b69afe4ce9
-- title:
--   Col: norm uc le
-- statement:
--   The Col construction uses the norm uc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L68-L80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex NumberField
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {E : Type} [Field E] [NumberField E]
variable (X : PT E) (I : Submodule ℤ (Vsp X.dim))
variable {X I}

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.norm_uc_le (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (v : Vsp X.dim) :
    ‖uc (IR I) v‖ ≤ ‖v‖ := by sorry
