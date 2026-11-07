-- Prove2me | Theorems.Thm_QEC_Locality_daiLiTenthCore_complement_subset_exterior
-- name    : QEC.Locality.daiLiTenthCore_complement_subset_exterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:06:47.387746+00:00
-- url     : https://prove2.me/theorems/7aa2a363-29ea-460a-9623-4ef47a30b120
-- title:
--   Locality: dai Li Tenth Core complement subset exterior
-- statement:
--   The complement of the actual central rectangle is covered by its four
--   strict tenth-coordinate exterior tails.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L528-L558
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L528-L558

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

theorem QEC.Locality.daiLiTenthCore_complement_subset_exterior
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) :
    region \ daiLiTenthCore embedding region hRegion ⊆
      daiLiTenthExterior embedding region hRegion := by sorry
