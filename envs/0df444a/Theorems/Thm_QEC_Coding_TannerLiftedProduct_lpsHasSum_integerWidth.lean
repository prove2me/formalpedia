-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHasSum_integerWidth
-- name    : QEC.Coding.TannerLiftedProduct.lpsHasSum_integerWidth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:40.638911+00:00
-- url     : https://prove2.me/theorems/c78451f1-a955-4c49-b9ce-487d5d1de994
-- title:
--   Tanner Lifted Product: lps Has Sum integer Width
-- statement:
--   The expanded actual unit-width coefficients sum to the original modular form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFourierPeriodChange.lean#L28-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFourierPeriodChange.lean#L28-L49

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsHasSum_integerWidth (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)
    (h1 : (1:ℝ)∈Γ.strictPeriods) (m : ℕ) (hm : 0 < m) (f : ModularForm Γ k) (z : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n
      ((UpperHalfPlane.qExpansion 1 f).expand m hm.ne')*
        Function.Periodic.qParam (m:ℝ) (z:ℂ)^n) (f z) := by sorry
