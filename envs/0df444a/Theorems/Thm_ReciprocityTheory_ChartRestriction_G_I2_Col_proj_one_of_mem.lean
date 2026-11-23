-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_proj_one_of_mem
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.proj_one_of_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:12.305938+00:00
-- url     : https://prove2.me/theorems/dc60309e-8fa6-488a-93c7-d63776343265
-- title:
--   Col: proj one of mem
-- statement:
--   The Col construction uses the proj one of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L105-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L105-L117

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.proj_one_of_mem {K : Submodule ℝ (Vsp X.dim)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    {a : Vsp X.dim} (ha : a ∈ K) : p1 K a = a := by sorry
