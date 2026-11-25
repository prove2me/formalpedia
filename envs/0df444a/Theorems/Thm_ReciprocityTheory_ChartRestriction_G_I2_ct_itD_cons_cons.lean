-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_itD_cons_cons
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_itD_cons_cons
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:50.647801+00:00
-- url     : https://prove2.me/theorems/b2a8c909-fe03-489c-992e-b8e5b9423bb6
-- title:
--   I2: ct it D cons cons
-- statement:
--   The I2 construction uses the ct it D cons cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L151-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L151-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
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
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_itD_cons_cons {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (a b : W) (l : List W) (z : W) :
    itD f (a :: b :: l) z = fderiv ℂ (fderiv ℂ (fun y => itD f l y)) z a b := by sorry
