-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_add_left
-- name    : ReciprocityTheory.ChartRestriction.G.I2.actE_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:39.401936+00:00
-- url     : https://prove2.me/theorems/a053b776-25da-4f79-93ee-b6f7300c4dd2
-- title:
--   I2: act E add left
-- statement:
--   The I2 construction uses the act E add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L40-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
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
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}

theorem ReciprocityTheory.ChartRestriction.G.I2.actE_add_left (β γ : E) (v : Vsp dim) : actE (β + γ) v = actE β v + actE γ v := by sorry
