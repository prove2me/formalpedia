-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQExpansion_integerWidth_order
-- name    : QEC.Coding.TannerLiftedProduct.lpsQExpansion_integerWidth_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:19.787303+00:00
-- url     : https://prove2.me/theorems/50969ea1-a527-4e3a-9709-f9f9101746dc
-- title:
--   Tanner Lifted Product: lps QExpansion integer Width order
-- statement:
--   An integer change of width multiplies the actual Fourier order, including infinite order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFourierPeriodChange.lean#L63-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFourierPeriodChange.lean#L63-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsQExpansion_integerWidth_order (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)
    (h1 : (1:ℝ)∈Γ.strictPeriods) (m : ℕ) (hm : 0 < m) (f : ModularForm Γ k) :
    (UpperHalfPlane.qExpansion (m:ℝ) f).order=m • (UpperHalfPlane.qExpansion 1 f).order := by sorry
