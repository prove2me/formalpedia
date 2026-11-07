-- Prove2me | Theorems.Thm_QEC_Locality_daiLi_lt_separatorBandCount
-- name    : QEC.Locality.daiLi_lt_separatorBandCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:43.74589+00:00
-- url     : https://prove2.me/theorems/7060cc22-444d-4354-a1d3-cacc92b8ab75
-- title:
--   Locality: dai Li lt separator Band Count
-- statement:
--   Under the source's positive length scale, the chosen number of bands is
--   strictly larger than `sqrt(n) / (8 ell)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L851-L859
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L851-L859

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

theorem QEC.Locality.daiLi_lt_separatorBandCount
    {ell : ℝ} {n : Nat} (hEll : 0 < ell) :
    Real.sqrt n / (8 * ell) < daiLiSeparatorBandCount ell n := by sorry
