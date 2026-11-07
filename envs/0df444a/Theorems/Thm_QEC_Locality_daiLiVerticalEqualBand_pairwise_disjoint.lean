-- Prove2me | Theorems.Thm_QEC_Locality_daiLiVerticalEqualBand_pairwise_disjoint
-- name    : QEC.Locality.daiLiVerticalEqualBand_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:20.374644+00:00
-- url     : https://prove2.me/theorems/d09301aa-e0f4-4b30-bf1b-5a55b7dfe7e6
-- title:
--   Locality: dai Li Vertical Equal Band pairwise disjoint
-- statement:
--   Distinct half-open equal-width vertical bands are disjoint whenever the
--   source interval has positive span.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L769-L791
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L769-L791

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

theorem QEC.Locality.daiLiVerticalEqualBand_pairwise_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper : ℝ} {m : Nat} (hM : 0 < m) (hSpan : 0 < upper - lower) :
    ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (daiLiVerticalEqualBand embedding region lower upper m) := by sorry
