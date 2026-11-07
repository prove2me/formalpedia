-- Prove2me | Theorems.Thm_QEC_Locality_daiLiVerticalSeparator_cover
-- name    : QEC.Locality.daiLiVerticalSeparator_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:55.817261+00:00
-- url     : https://prove2.me/theorems/eb685f9b-604e-4172-8deb-3fa25f469fc4
-- title:
--   Locality: dai Li Vertical Separator cover
-- statement:
--   Support-free vertical cuts partition their actual finite parent into three
--   disjointly owned pieces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1273-L1303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L1273-L1303

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

theorem QEC.Locality.daiLiVerticalSeparator_cover
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut) :
    daiLiVerticalSeparatorLower embedding region lowerCut ∪
        daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiVerticalSeparatorUpper embedding region upperCut = region := by sorry
