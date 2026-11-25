-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_pi_diff
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_pi_diff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:07.473419+00:00
-- url     : https://prove2.me/theorems/6fd3f975-52d4-4ac4-b9e9-2aa51dcc9a39
-- title:
--   I2: n A pi diff
-- statement:
--   The I2 construction uses the n A pi diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L234-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L234-L238

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

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_pi_diff {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (k : Fin n) :
    Differentiable ℂ (fun v : Fin n → Vsp X.dim => fun _ : Fin 1 => π (v k)) := by sorry
