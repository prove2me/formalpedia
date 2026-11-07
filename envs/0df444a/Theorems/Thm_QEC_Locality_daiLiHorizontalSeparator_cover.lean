-- Prove2me | Theorems.Thm_QEC_Locality_daiLiHorizontalSeparator_cover
-- name    : QEC.Locality.daiLiHorizontalSeparator_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:26.173205+00:00
-- url     : https://prove2.me/theorems/690c3fe2-2fee-4ca7-9e54-5be8cfe1fa73
-- title:
--   Locality: dai Li Horizontal Separator cover
-- statement:
--   The three actual pieces cover the parent region when both selected lines
--   are support-free.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1124-L1154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1124-L1154

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

theorem QEC.Locality.daiLiHorizontalSeparator_cover
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut) :
    daiLiHorizontalSeparatorLower embedding region lowerCut ∪
        daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiHorizontalSeparatorUpper embedding region upperCut = region := by sorry
