-- Prove2me | Theorems.Thm_QEC_Locality_no_fixedGeneratorInteraction_from_outside_longEndpoints_of_threshold_lt_one
-- name    : QEC.Locality.no_fixedGeneratorInteraction_from_outside_longEndpoints_of_threshold_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:59:55.333631+00:00
-- url     : https://prove2.me/theorems/247c7c96-5c59-4557-91cb-1d0ce6bf34f2
-- title:
--   Locality: no fixed Generator Interaction from outside long Endpoints of threshold lt one
-- statement:
--   A vertex outside the actual long-endpoint set cannot participate in any
--   fixed-generator interaction when the Part-I threshold is below one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L111-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L111-L122

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

theorem QEC.Locality.no_fixedGeneratorInteraction_from_outside_longEndpoints_of_threshold_lt_one
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {threshold : ℝ}
    (hThreshold : threshold < 1) {p q : ι}
    (hp : p ∉ longInteractionEndpointQubits P embedding threshold)
    (hInteraction : P.fixedGeneratorInteraction p q) : False := by sorry
