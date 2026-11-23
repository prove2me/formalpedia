-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_eq_inner
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_eq_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:39.586501+00:00
-- url     : https://prove2.me/theorems/ce4ee250-516b-45f4-8263-0596134116dc
-- title:
--   Col: Hf eq inner
-- statement:
--   The Col construction uses the Hf eq inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L182-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L182-L183

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_eq_inner (v w : EuclideanSpace ℂ ι) : Hf v w = ⟪w, v⟫_ℂ := by sorry
