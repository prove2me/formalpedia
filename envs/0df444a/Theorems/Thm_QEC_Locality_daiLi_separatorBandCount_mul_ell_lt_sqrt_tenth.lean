-- Prove2me | Theorems.Thm_QEC_Locality_daiLi_separatorBandCount_mul_ell_lt_sqrt_tenth
-- name    : QEC.Locality.daiLi_separatorBandCount_mul_ell_lt_sqrt_tenth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:00:19.139456+00:00
-- url     : https://prove2.me/theorems/26c8c983-aaa1-4395-85db-e2343da379b6
-- title:
--   Locality: dai Li separator Band Count mul ell lt sqrt tenth
-- statement:
--   In the `ell >= 1` source regime, the selected band count leaves strictly
--   more than `ell` of geometric width before the wide-axis endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L863-L900
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L863-L900

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.daiLi_separatorBandCount_mul_ell_lt_sqrt_tenth
    {ell : ℝ} {n : Nat} (hN : 0 < n) (hEll : 0 < ell)
    (hScale : ell ≤ Real.sqrt n / 8) :
    (daiLiSeparatorBandCount ell n : ℝ) * ell < Real.sqrt ((n : ℝ) / 10) := by sorry
