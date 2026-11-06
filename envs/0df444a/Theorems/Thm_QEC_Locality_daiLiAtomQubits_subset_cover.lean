-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomQubits_subset_cover
-- name    : QEC.Locality.daiLiAtomQubits_subset_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:42.468922+00:00
-- url     : https://prove2.me/theorems/92b41354-2177-4342-8384-db8eda8f1213
-- title:
--   Locality: dai Li Atom Qubits subset cover
-- statement:
--   The Locality construction uses the dai Li Atom Qubits subset cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L518-L524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L518-L524

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

theorem QEC.Locality.daiLiAtomQubits_subset_cover
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (atoms : List (ℝ × ℝ)) (atom : ℝ × ℝ) (hAtom : atom ∈ atoms) :
    daiLiAtomQubits embedding left right atom ⊆
      daiLiAtomQubitsCover embedding left right atoms := by sorry
