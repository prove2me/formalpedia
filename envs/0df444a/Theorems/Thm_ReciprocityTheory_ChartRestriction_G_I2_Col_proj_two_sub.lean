-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_proj_two_sub
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.proj_two_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:27:09.455701+00:00
-- url     : https://prove2.me/theorems/67c614ab-3fbb-4eb2-a184-0a88eb1feafb
-- title:
--   Col: proj two sub
-- statement:
--   The Col construction uses the proj two sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L62-L63

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.proj_two_sub (K : Submodule ℝ (Vsp X.dim)) (x y : Vsp X.dim) : p2 K (x - y) = p2 K x - p2 K y := by sorry
