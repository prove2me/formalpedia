-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_iter_cexp
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_iter_cexp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:40.93457+00:00
-- url     : https://prove2.me/theorems/1723ec4e-2cac-432e-91a4-ca7fb9b96562
-- title:
--   I2: ct iter cexp
-- statement:
--   The I2 construction uses the ct iter cexp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L61-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L61-L82

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

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_iter_cexp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ℓ : V →L[ℂ] ℂ) (n : ℕ) :
    iteratedFDeriv ℂ n (fun w => cexp (ℓ w)) =
      fun v => cexp (ℓ v) • (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap
        (fun _ => ℓ) := by sorry
