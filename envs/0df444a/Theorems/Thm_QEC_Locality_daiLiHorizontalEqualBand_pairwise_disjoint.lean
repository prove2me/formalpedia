-- Prove2me | Theorems.Thm_QEC_Locality_daiLiHorizontalEqualBand_pairwise_disjoint
-- name    : QEC.Locality.daiLiHorizontalEqualBand_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:07:26.033871+00:00
-- url     : https://prove2.me/theorems/2023bd41-a8b1-4d8d-b0c7-652f75845066
-- title:
--   Locality: dai Li Horizontal Equal Band pairwise disjoint
-- statement:
--   The Locality construction uses the dai Li Horizontal Equal Band pairwise disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L986-L1008
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L986-L1008

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

theorem QEC.Locality.daiLiHorizontalEqualBand_pairwise_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper : ℝ} {m : Nat} (hM : 0 < m) (hSpan : 0 < upper - lower) :
    ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (daiLiHorizontalEqualBand embedding region lower upper m) := by sorry
