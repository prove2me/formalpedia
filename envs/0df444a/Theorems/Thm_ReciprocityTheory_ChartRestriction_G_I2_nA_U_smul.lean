-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_U_smul
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_U_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:35.715422+00:00
-- url     : https://prove2.me/theorems/edebf854-8055-404b-b694-9f37a333cb4c
-- title:
--   I2: n A U smul
-- statement:
--   The I2 construction uses the n A U smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L328-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L328-L330

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

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_U_smul (q : ℕ) {n : ℕ} (a : Fin n → Vsp X.dim) (c : ℂ) (F : (Fin n → Vsp X.dim) → ℂ) :
    X.U q a (fun v => c * F v) = fun v => c * X.U q a F v := by sorry
