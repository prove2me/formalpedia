-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiTenthCore_rectangle
-- name    : QEC.Locality.mem_daiLiTenthCore_rectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:06:47.60317+00:00
-- url     : https://prove2.me/theorems/283e3c7e-1e6e-4af3-8c94-714f7aa8e223
-- title:
--   Locality: mem dai Li Tenth Core rectangle
-- statement:
--   Every retained central point is geometrically contained in its concrete
--   tenth-coordinate rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L661-L669
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L661-L669

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
omit [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.mem_daiLiTenthCore_rectangle
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) {q : ι}
    (hq : q ∈ daiLiTenthCore embedding region hRegion) :
    embedding.point q ∈ rectangle
      (daiLiTenthCoreLower embedding region hRegion)
      (daiLiTenthCoreUpper embedding region hRegion) := by sorry
