-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_proj_two_of_mem
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.proj_two_of_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:27:19.246721+00:00
-- url     : https://prove2.me/theorems/0aba4cbb-7c2d-42a3-83fd-41739ab1a794
-- title:
--   Col: proj two of mem
-- statement:
--   The Col construction uses the proj two of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L119-L121

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
variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.proj_two_of_mem {K : Submodule ℝ (Vsp X.dim)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    {a : Vsp X.dim} (ha : a ∈ K) : p2 K a = 0 := by sorry
