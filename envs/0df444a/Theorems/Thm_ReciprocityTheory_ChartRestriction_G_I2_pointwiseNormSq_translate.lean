-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pointwiseNormSq_translate
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pointwiseNormSq_translate
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:51.128219+00:00
-- url     : https://prove2.me/theorems/8d1c795f-1d08-4cd9-811a-4fc07cc2e88d
-- title:
--   I2: pointwise Norm Sq translate
-- statement:
--   The I2 construction uses the pointwise Norm Sq translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L116-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L116-L123

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)

theorem ReciprocityTheory.ChartRestriction.G.I2.pointwiseNormSq_translate (q : ℕ) {n : ℕ} (a : Fin n → Vsp X.dim) (F : (Fin n → Vsp X.dim) → ℂ)
    (v : Fin n → Vsp X.dim) : X.ptN2 q (X.U q a F) v = X.ptN2 q F (v - a) := by sorry
