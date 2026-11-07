-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiHorizontalLowBand
-- name    : QEC.Locality.exists_daiLiHorizontalLowBand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:34.951192+00:00
-- url     : https://prove2.me/theorems/67a0a1a1-04fa-4081-874d-a67397554ac6
-- title:
--   Locality: exists dai Li Horizontal Low Band
-- statement:
--   The Locality construction uses the exists dai Li Horizontal Low Band property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1051-L1087
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1051-L1087

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

theorem QEC.Locality.exists_daiLiHorizontalLowBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {ell lower upper : ℝ} {n : Nat}
    (hN : 0 < n) (hEll : 0 < ell) (hScale : ell ≤ Real.sqrt n / 8)
    (hCard : region.card ≤ n)
    (hSpan : Real.sqrt ((n : ℝ) / 10) < upper - lower) :
    ∃ i : Fin (daiLiSeparatorBandCount ell n),
      ell < daiLiVerticalBandUpper lower upper (daiLiSeparatorBandCount ell n) i -
        daiLiVerticalBandLower lower upper (daiLiSeparatorBandCount ell n) i ∧
      ((daiLiHorizontalEqualBand embedding region lower upper
        (daiLiSeparatorBandCount ell n) i).card : ℝ) ≤
        8 * ell * Real.sqrt n := by sorry
