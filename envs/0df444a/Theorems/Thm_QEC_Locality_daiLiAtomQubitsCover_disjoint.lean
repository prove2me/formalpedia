-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomQubitsCover_disjoint
-- name    : QEC.Locality.daiLiAtomQubitsCover_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:07:05.749839+00:00
-- url     : https://prove2.me/theorems/8574ca15-caec-4e06-873b-0a1333e9c356
-- title:
--   Locality: dai Li Atom Qubits Cover disjoint
-- statement:
--   The Locality construction uses the dai Li Atom Qubits Cover disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1438-L1453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1438-L1453

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem QEC.Locality.daiLiAtomQubitsCover_disjoint
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (first second : List (ℝ × ℝ))
    (hDisjoint : ∀ firstAtom ∈ first, ∀ secondAtom ∈ second,
      Disjoint (daiLiAtomQubits embedding left right firstAtom)
        (daiLiAtomQubits embedding left right secondAtom)) :
    Disjoint (daiLiAtomQubitsCover embedding left right first)
      (daiLiAtomQubitsCover embedding left right second) := by sorry
