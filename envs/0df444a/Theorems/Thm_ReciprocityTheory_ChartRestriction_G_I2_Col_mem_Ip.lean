-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_mem_Ip
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.mem_Ip
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:26:44.497222+00:00
-- url     : https://prove2.me/theorems/bfe42aa6-68f6-5671-91da-98fc6f8b2f3a
-- title:
--   Col: mem Ip
-- statement:
--   The Col construction uses the mem Ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L32-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/MemOfProjTwoEqZero.lean#L32-L32

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

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.mem_Ip {x : Vsp X.dim} : x ∈ Ip X I ↔ x ∈ X.L ∧ ∀ a ∈ I, (Hf x a).im = 0 := by sorry
