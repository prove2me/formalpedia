-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_act_eq_actE
-- name    : ReciprocityTheory.ChartRestriction.G.I2.act_eq_actE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:48.643991+00:00
-- url     : https://prove2.me/theorems/dc80cfb8-0a2b-42aa-a044-e0525d2771a2
-- title:
--   I2: act eq act E
-- statement:
--   The I2 construction uses the act eq act E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L18-L18

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

theorem ReciprocityTheory.ChartRestriction.G.I2.act_eq_actE (α : 𝓞 E) (v : Vsp dim) : act α v = actE (α : E) v := by sorry
