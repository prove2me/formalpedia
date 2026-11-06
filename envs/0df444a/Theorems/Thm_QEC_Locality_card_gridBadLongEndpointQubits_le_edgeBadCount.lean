-- Prove2me | Theorems.Thm_QEC_Locality_card_gridBadLongEndpointQubits_le_edgeBadCount
-- name    : QEC.Locality.card_gridBadLongEndpointQubits_le_edgeBadCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:42.618317+00:00
-- url     : https://prove2.me/theorems/702b1cb6-546f-49ca-878e-70a162da9fc6
-- title:
--   Locality: card grid Bad Long Endpoint Qubits le edge Bad Count
-- statement:
--   Deduplicating actual long-incidence endpoints can only lower their count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1856-L1864
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1856-L1864

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.card_gridBadLongEndpointQubits_le_edgeBadCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    (gridBadLongEndpointQubits P embedding threshold w ell t).card ≤
      edgeBadCount w (2 * ell)
        (P.daiLiLongIncidencePoint embedding threshold) t := by sorry
