-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiDGeKExceptionalBadQubits_lt_distance
-- name    : QEC.Locality.card_daiLiDGeKExceptionalBadQubits_lt_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:25.360201+00:00
-- url     : https://prove2.me/theorems/437e2185-96f5-4ce6-bd74-5f66ec1bb436
-- title:
--   Locality: card dai Li DGe KExceptional Bad Qubits lt distance
-- statement:
--   The exceptional bad set is small whenever the actual *unordered* long-edge
--   count is small.  The factor two is discharged from the interaction graph's
--   degree-sum theorem, rather than being supplied by a caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L473-L487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L473-L487

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

theorem QEC.Locality.card_daiLiDGeKExceptionalBadQubits_lt_distance
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (d : ℕ)
    (hLongCount : 2 * P.longInteractionCount embedding threshold < d) :
    (daiLiDGeKExceptionalBadQubits P embedding threshold w ell t).card < d := by sorry
