-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_proj_one_mem_realSpan
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.proj_one_mem_realSpan
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:26:49.259429+00:00
-- url     : https://prove2.me/theorems/31052dec-b066-52fb-84cd-5c2af05beb83
-- title:
--   Col: proj one mem real Span
-- statement:
--   The Col construction uses the proj one mem real Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L49-L54

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.proj_one_mem_realSpan {x : Vsp X.dim} (hx : x ∈ Ip X I) : p1 (IR I) x ∈ IR I := by sorry
