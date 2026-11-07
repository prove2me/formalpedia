-- Prove2me | Theorems.Thm_QEC_Locality_daiLiLargeDistance_totalIncidence_budget
-- name    : QEC.Locality.daiLiLargeDistance_totalIncidence_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:51.064266+00:00
-- url     : https://prove2.me/theorems/b3743e2a-742a-414d-a0f3-e53f7e77ce3f
-- title:
--   Locality: dai Li Large Distance total Incidence budget
-- statement:
--   The source's few-long-interactions assumption bounds the total actual
--   endpoint incidence counter.  This uses the proved degree-sum identity for the
--   same unordered interaction set, rather than an ordered-pair substitute.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L55-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L55-L65

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

theorem QEC.Locality.daiLiLargeDistance_totalIncidence_budget
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d) :
    10 * (∑ q : ι,
      P.daiLiInteractionCounter embedding
        (daiLiLargeDistanceThreshold d (Fintype.card ι)) q) ≤ d := by sorry
