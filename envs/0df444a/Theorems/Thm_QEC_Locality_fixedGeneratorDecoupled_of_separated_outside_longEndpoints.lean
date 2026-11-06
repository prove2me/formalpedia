-- Prove2me | Theorems.Thm_QEC_Locality_fixedGeneratorDecoupled_of_separated_outside_longEndpoints
-- name    : QEC.Locality.fixedGeneratorDecoupled_of_separated_outside_longEndpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:45:18.8954+00:00
-- url     : https://prove2.me/theorems/d0d095da-08b4-4d9e-bf44-8ad98059a86b
-- title:
--   Locality: fixed Generator Decoupled of separated outside long Endpoints
-- statement:
--   Two concrete regions are fixed-generator decoupled when they are disjoint,
--   every selected qubit is outside the actual threshold-long endpoint set, and
--   their embedded points are separated by the threshold.  The proof splits a
--   putative cross interaction into its long and short cases; it does not assume
--   that ``good'' interactions exhaust the fixed-generator interaction graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2029-L2047
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2029-L2047

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

theorem QEC.Locality.fixedGeneratorDecoupled_of_separated_outside_longEndpoints
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (left right : Finset ι)
    (hDisjoint : Disjoint left right)
    (hLeftOutside : left ⊆ (longInteractionEndpointQubits P embedding threshold)ᶜ)
    (hRightOutside : right ⊆ (longInteractionEndpointQubits P embedding threshold)ᶜ)
    (hSeparated : ∀ p ∈ left, ∀ q ∈ right,
      threshold ≤ embedding.distance p q) :
    P.fixedGeneratorDecoupled (left : Set ι) (right : Set ι) := by sorry
