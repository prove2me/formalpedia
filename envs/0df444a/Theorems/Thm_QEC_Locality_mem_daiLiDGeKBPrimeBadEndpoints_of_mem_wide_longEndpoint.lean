-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiDGeKBPrimeBadEndpoints_of_mem_wide_longEndpoint
-- name    : QEC.Locality.mem_daiLiDGeKBPrimeBadEndpoints_of_mem_wide_longEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:14.751465+00:00
-- url     : https://prove2.me/theorems/9755284b-5031-4a24-83e8-54ca78a8c92b
-- title:
--   Locality: mem dai Li DGe KBPrime Bad Endpoints of mem wide long Endpoint
-- statement:
--   A threshold-long endpoint lying in the actual wider `B'` buffer is selected
--   by the bad-incidence construction.  This is the formal `B'`-to-`C` routing
--   step in DL24 Case 2.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L296-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L296-L314

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK

theorem QEC.Locality.mem_daiLiDGeKBPrimeBadEndpoints_of_mem_wide_longEndpoint
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (q : ι)
    (hWide : q ∈ daiLiDGeKBPrimeQubits embedding w ell t)
    (hLong : q ∈ longInteractionEndpointQubits P embedding threshold) :
    q ∈ daiLiDGeKBPrimeBadEndpoints P embedding threshold w ell t := by sorry
