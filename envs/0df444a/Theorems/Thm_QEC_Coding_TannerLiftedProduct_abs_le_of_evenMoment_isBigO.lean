-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_of_evenMoment_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.abs_le_of_evenMoment_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:19.88191+00:00
-- url     : https://prove2.me/theorems/668ec8af-841f-4130-b59d-05e462064283
-- title:
--   Tanner Lifted Product: abs le of even Moment is Big O
-- statement:
--   A big-O bound for a finite nonnegative even spectral moment controls
--   each individual spectral value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMomentBound.lean#L88-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSMomentBound.lean#L88-L109

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
set_option autoImplicit false
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.abs_le_of_evenMoment_isBigO
    {I : Type*} [Fintype I] (eigenvalue : I → ℝ)
    {r : ℝ} (hr : 0 ≤ r)
    (hMoment : ∀ s : ℝ, r < s →
      (fun n : ℕ => ∑ i, |eigenvalue i| ^ (2 * n)) =O[atTop]
        fun n : ℕ => s ^ (2 * n)) :
    ∀ i, |eigenvalue i| ≤ r := by sorry
