-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_inner_uc
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.inner_uc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:36.618346+00:00
-- url     : https://prove2.me/theorems/8e7c55e1-ae39-4c8b-9b96-5a572316a988
-- title:
--   Col: inner uc
-- statement:
--   The Col construction uses the inner uc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L172-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L172-L180

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {ι : Type} [Fintype ι]
variable (K : Submodule ℝ (EuclideanSpace ℂ ι))

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.inner_uc (v : EuclideanSpace ℂ ι) (a : EuclideanSpace ℂ ι) (ha : a ∈ K) :
    ⟪uc K v, a⟫_ℝ = (Hf v a).im := by sorry
