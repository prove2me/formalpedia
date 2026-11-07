-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiGridSideGoodFamily
-- name    : QEC.Locality.exists_erasureRecovery_daiLiGridSideGoodFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:15:15.628895+00:00
-- url     : https://prove2.me/theorems/9437ff6a-c181-4301-bdd9-ce1b9c97047c
-- title:
--   Locality: exists erasure Recovery dai Li Grid Side Good Family
-- statement:
--   A typed CPTP erasure recovery for the union of any finite family of good
--   grid sides.  Each component is recovered from semantic distance and the union
--   is recovered through actual fixed-generator decoupling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1913-L1943
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1913-L1943

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable

theorem QEC.Locality.exists_erasureRecovery_daiLiGridSideGoodFamily
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    {w ell : ℝ} (hEll : 0 < ell) (hWidth : 4 * ell ≤ w)
    (threshold : ℝ) (hThreshold : threshold ≤ ell)
    (origin : ℝ × ℝ) (s : Finset DaiLiGridSideIndex)
    (hEdge : 1 ≤ 2 * ell) (hLong : 1 ≤ w - 4 * ell)
    (hSmall : 12 * ell * (w - 4 * ell) < d) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem (daiLiGridSideGoodFamily P embedding threshold w ell origin) s).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem (daiLiGridSideGoodFamily P embedding threshold w ell origin) s).complementSystem
        P.semanticCode
        (familyUnionSubsystem (daiLiGridSideGoodFamily P embedding threshold w ell origin) s).erasureChannelFromRegister
        recovery := by sorry
