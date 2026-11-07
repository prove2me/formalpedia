-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiLargeDistance_threshold_lt_one
-- name    : QEC.Locality.exists_erasureRecovery_daiLiLargeDistance_threshold_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:05:18.742313+00:00
-- url     : https://prove2.me/theorems/864fe210-8ba8-4c79-b8d1-a9dee9a8921f
-- title:
--   Locality: exists erasure Recovery dai Li Large Distance threshold lt one
-- statement:
--   The `ell < 1` source corner constructs a concrete recovery after erasure
--   of every physical qubit.  The construction has no supplied recovery or
--   interaction partition: the exceptional set is the actual long-endpoint set,
--   and its complement is assembled from concrete singleton recoveries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L152-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L152-L225

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

theorem QEC.Locality.exists_erasureRecovery_daiLiLargeDistance_threshold_lt_one
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d)
    (hdTwo : 2 ≤ d)
    (hThreshold : daiLiLargeDistanceThreshold d (Fintype.card ι) < 1) :
    ∃ recovery : QuantumChannel
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)).erasureChannelFromRegister
        recovery := by sorry
