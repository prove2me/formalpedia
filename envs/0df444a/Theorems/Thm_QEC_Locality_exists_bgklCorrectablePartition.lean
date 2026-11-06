-- Prove2me | Theorems.Thm_QEC_Locality_exists_bgklCorrectablePartition
-- name    : QEC.Locality.exists_bgklCorrectablePartition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:03:02.05969+00:00
-- url     : https://prove2.me/theorems/d30abfcb-4d59-4244-8e47-b429521b337c
-- title:
--   Locality: exists bgkl Correctable Partition
-- statement:
--   The internal `0 < c < 1` BGKL correctable-set bridge.  Its three branches are
--   explicit: small distance uses the empty correctable set, oversized scale uses
--   the whole vertex set, and the nondegenerate branch consumes #494's finite edge
--   division before applying #382 and #373.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/Core.lean#L664-L893
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/Core.lean#L664-L893

import Definitions.Def_QEC_Locality_SeparatorProfile_ExplicitDivision
import Definitions.Def_QEC_Locality_CorrectablePartition_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.exists_bgklCorrectablePartition
    (beta exponent : ℝ) (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        {κ : Type v} [Fintype κ]
        (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
        (d : Nat), 0 < d → d ≤ Fintype.card ι →
        StabilizerCode.SemanticStabilizerDistance P.code d →
        P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent →
        ∃ A : Finset ι, ∃ recovery : QuantumChannel (finiteSubsystemOfFinset A).complementSystem
            (Qubit.QubitRegister ι),
          Correctable (Qubit.QubitRegister ι) (finiteSubsystemOfFinset A).complementSystem
            P.semanticCode (finiteSubsystemOfFinset A).erasureChannelFromRegister recovery ∧
          ((Finset.univ \ A).card : ℝ) ≤ alpha * Fintype.card ι /
            Real.rpow d ((1 - exponent) / exponent) := by sorry
