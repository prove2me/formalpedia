-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiVerticalLowBand
-- name    : QEC.Locality.exists_daiLiVerticalLowBand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:04.23227+00:00
-- url     : https://prove2.me/theorems/6418f691-1db4-4cb3-a5d8-84e57f431f29
-- title:
--   Locality: exists dai Li Vertical Low Band
-- statement:
--   Source-faithful equal-band selection in one already-wide vertical axis.
--   The index is constructed by the finite pigeonhole argument, and the returned
--   width is strict so it can be support-free perturbed without enlarging the
--   selected strip.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L937-L973
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L937-L973

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

theorem QEC.Locality.exists_daiLiVerticalLowBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {ell lower upper : ℝ} {n : Nat}
    (hN : 0 < n) (hEll : 0 < ell) (hScale : ell ≤ Real.sqrt n / 8)
    (hCard : region.card ≤ n)
    (hSpan : Real.sqrt ((n : ℝ) / 10) < upper - lower) :
    ∃ i : Fin (daiLiSeparatorBandCount ell n),
      ell < daiLiVerticalBandUpper lower upper (daiLiSeparatorBandCount ell n) i -
        daiLiVerticalBandLower lower upper (daiLiSeparatorBandCount ell n) i ∧
      ((daiLiVerticalEqualBand embedding region lower upper
        (daiLiSeparatorBandCount ell n) i).card : ℝ) ≤
        8 * ell * Real.sqrt n := by sorry
