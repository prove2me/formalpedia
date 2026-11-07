-- Prove2me | Theorems.Thm_QEC_Locality_card_longInteractionEndpointQubits_lt_distance
-- name    : QEC.Locality.card_longInteractionEndpointQubits_lt_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:05:11.691256+00:00
-- url     : https://prove2.me/theorems/ffd62d0f-c89e-4bf8-9d13-7130f477b411
-- title:
--   Locality: card long Interaction Endpoint Qubits lt distance
-- statement:
--   The few-long-interaction hypothesis makes the actual endpoint set strictly
--   smaller than the distance in the nontrivial source branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L94-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L94-L107

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

theorem QEC.Locality.card_longInteractionEndpointQubits_lt_distance
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d) (hd : 0 < d) :
    (longInteractionEndpointQubits P embedding
      (daiLiLargeDistanceThreshold d (Fintype.card ι))).card < d := by sorry
