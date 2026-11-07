-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_parseval_int
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_parseval_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:18:08.862197+00:00
-- url     : https://prove2.me/theorems/845c4adf-6578-44f6-8de0-83a3c09d7c76
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Circle parseval int
-- statement:
--   Actual Hilbert-space Parseval identifies the sum over all integer frequencies with its square integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L225-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L225-L237

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_parseval_int (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun k : ℤ => ‖fourierCoeff (lpsCuspHorocycleCircle N f y) k‖^2)
      (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle) := by sorry
