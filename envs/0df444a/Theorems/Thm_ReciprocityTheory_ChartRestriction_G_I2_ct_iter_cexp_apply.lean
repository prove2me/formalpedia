-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_iter_cexp_apply
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_iter_cexp_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:03.916125+00:00
-- url     : https://prove2.me/theorems/606f433e-10a4-5ce8-8ddd-87dcfbdb7b03
-- title:
--   I2: ct iter cexp apply
-- statement:
--   The I2 construction uses the ct iter cexp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L84-L88

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

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_iter_cexp_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ℓ : V →L[ℂ] ℂ) (n : ℕ) (v : V) (x : Fin n → V) :
    iteratedFDeriv ℂ n (fun w => cexp (ℓ w)) v x = cexp (ℓ v) * ∏ k, ℓ (x k) := by sorry
