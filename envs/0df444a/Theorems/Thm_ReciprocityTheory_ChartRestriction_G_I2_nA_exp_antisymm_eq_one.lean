-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_exp_antisymm_eq_one
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_exp_antisymm_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:45.260799+00:00
-- url     : https://prove2.me/theorems/5a54520a-63f5-5928-b337-06bc4b9b8216
-- title:
--   I2: n A exp antisymm eq one
-- statement:
--   The I2 construction uses the n A exp antisymm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L191-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L191-L200

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

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_exp_antisymm_eq_one {n : ℕ} (q : ℕ) (γ b : Fin n → Vsp X.dim) (m : ℤ)
    (hm : (q : ℝ) * (HC γ b).im = m) :
    cexp ((q : ℂ) * Real.pi * (HC γ b - HC b γ)) = 1 := by sorry
