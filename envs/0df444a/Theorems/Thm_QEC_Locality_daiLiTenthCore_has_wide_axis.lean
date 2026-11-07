-- Prove2me | Theorems.Thm_QEC_Locality_daiLiTenthCore_has_wide_axis
-- name    : QEC.Locality.daiLiTenthCore_has_wide_axis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:06:43.935015+00:00
-- url     : https://prove2.me/theorems/32035df9-9b34-4a95-8075-9939f3841892
-- title:
--   Locality: dai Li Tenth Core has wide axis
-- statement:
--   The source's geometric wide-axis conclusion for the actual central
--   tenth-coordinate rectangle.  It follows from the proved finite packing
--   inequality, including the small-side corner through the expanded-box bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L675-L753
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L675-L753

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
omit [Fintype ι]

theorem QEC.Locality.daiLiTenthCore_has_wide_axis
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) (hTen : 10 ≤ region.card) :
    Real.sqrt ((region.card : ℝ) / 10) <
        (daiLiTenthCoreUpper embedding region hRegion).1 -
          (daiLiTenthCoreLower embedding region hRegion).1 ∨
      Real.sqrt ((region.card : ℝ) / 10) <
        (daiLiTenthCoreUpper embedding region hRegion).2 -
          (daiLiTenthCoreLower embedding region hRegion).2 := by sorry
