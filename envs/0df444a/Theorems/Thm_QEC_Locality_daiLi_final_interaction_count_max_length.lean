-- Prove2me | Theorems.Thm_QEC_Locality_daiLi_final_interaction_count_max_length
-- name    : QEC.Locality.daiLi_final_interaction_count_max_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:32:16.448196+00:00
-- url     : https://prove2.me/theorems/c21da7ac-84de-4581-9699-3741f4d87845
-- title:
--   Locality: dai Li final interaction count max length
-- statement:
--   Final internal Dai--Li handoff.  The source assumptions choose the unit
--   base rectangles and finite growth steps, and the project-owned above-BPT
--   witness discharges all low-scale packing and grid inequalities internally.
--   The conclusion counts the actual distinct unordered interactions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/FinalComposition.lean#L427-L513
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/FinalComposition.lean#L427-L513

import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Definitions.Def_QEC_Locality_OptimalTradeoff_FinalComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.daiLi_final_interaction_count_max_length
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hD : 0 < d) (hEncodedPositive : 0 < P.encodedQubits)
    (hAboveBPT : daiLiFinalAboveBPTConstant * Fintype.card ι ≤
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2) :
    max (P.encodedQubits : ℝ) (d : ℝ) / 200 ≤
      (P.longInteractionCount embedding
        (daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d (Fintype.card ι) : ℝ) : ℝ) := by sorry
