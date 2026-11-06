-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiAtomQubitsCover
-- name    : QEC.Locality.mem_daiLiAtomQubitsCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:59:10.492415+00:00
-- url     : https://prove2.me/theorems/45e8d090-0c9e-4805-bc16-63eb84a79a98
-- title:
--   Locality: mem dai Li Atom Qubits Cover
-- statement:
--   The Locality construction uses the mem dai Li Atom Qubits Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L499-L516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L499-L516

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

theorem QEC.Locality.mem_daiLiAtomQubitsCover
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (atoms : List (ℝ × ℝ)) (q : ι) :
    q ∈ daiLiAtomQubitsCover embedding left right atoms ↔
      ∃ atom ∈ atoms, q ∈ daiLiAtomQubits embedding left right atom := by sorry
