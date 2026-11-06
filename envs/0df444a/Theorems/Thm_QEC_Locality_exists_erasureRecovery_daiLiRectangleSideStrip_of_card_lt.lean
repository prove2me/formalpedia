-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiRectangleSideStrip_of_card_lt
-- name    : QEC.Locality.exists_erasureRecovery_daiLiRectangleSideStrip_of_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:44:21.175319+00:00
-- url     : https://prove2.me/theorems/48915da4-3a40-4676-acb0-2770e27a1cac
-- title:
--   Locality: exists erasure Recovery dai Li Rectangle Side Strip of card lt
-- statement:
--   Any finite geometric side strip has a typed CPTP recovery once the
--   explicit packing bound is below the semantic distance.  This is the local
--   recovery used for `B`, not a recovery witness supplied by a partition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1802-L1818
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1802-L1818

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

theorem QEC.Locality.exists_erasureRecovery_daiLiRectangleSideStrip_of_card_lt
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell : ℝ) (lower upper : ℝ × ℝ) (side : Fin 4)
    (hCard : (daiLiRectangleSideStripQubits embedding ell lower upper side).card < d) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).complementSystem
        P.semanticCode
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).erasureChannelFromRegister
          recovery := by sorry
