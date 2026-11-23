-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_uc_add
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.uc_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:02.507366+00:00
-- url     : https://prove2.me/theorems/e7374ea6-61f7-49e7-8c2d-156ebff45910
-- title:
--   Col: uc add
-- statement:
--   The Col construction uses the uc add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L59-L60

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.uc_add (x y : Vsp X.dim) : uc (IR I) (x + y) = uc (IR I) x + uc (IR I) y := by sorry
