-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_caseDGeK_badQubits_edgeStrips
-- name    : QEC.Locality.exists_erasureRecovery_caseDGeK_badQubits_edgeStrips
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:46:47.547053+00:00
-- url     : https://prove2.me/theorems/b68135e3-905f-4466-9914-0f2eceb1af1a
-- title:
--   Locality: exists erasure Recovery case DGe K bad Qubits edge Strips
-- statement:
--   Source-faithful `d >= k` recovery composition for bad qubits plus edge strips.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2237-L2264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2237-L2264

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

theorem QEC.Locality.exists_erasureRecovery_caseDGeK_badQubits_edgeStrips
    {α : Type*} [DecidableEq α]
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (badQubits : FiniteSubsystem ι) (edgeStrips : α → FiniteSubsystem ι)
    (s : Finset α)
    (hCard : ∀ a, a ∈ caseDGeKPieceIndices s →
      (caseDGeKPieceFamily badQubits edgeStrips a).selected.card < d)
    (hDecoupled : ∀ a, a ∈ caseDGeKPieceIndices s →
      ∀ b, b ∈ caseDGeKPieceIndices s → a ≠ b →
        P.fixedGeneratorDecoupled
          ((caseDGeKPieceFamily badQubits edgeStrips a).selected : Set ι)
          ((caseDGeKPieceFamily badQubits edgeStrips b).selected : Set ι)) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
          (caseDGeKPieceIndices s)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
          (caseDGeKPieceIndices s)).complementSystem
        P.semanticCode
        (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
          (caseDGeKPieceIndices s)).erasureChannelFromRegister recovery := by sorry
