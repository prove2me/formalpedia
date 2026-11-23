-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_actE
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Hf_actE
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:43.35193+00:00
-- url     : https://prove2.me/theorems/93afd85d-e2b8-426b-ac32-9d5b43306cc3
-- title:
--   I2: Hf act E
-- statement:
--   The I2 construction uses the Hf act E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ActEMemSpanOmega.lean#L103-L108

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
variable [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.Hf_actE (β : E) (v w : Vsp dim) :
    Hf (actE β v) w = Hf v (actE (IsCMField.complexConj E β) w) := by sorry
