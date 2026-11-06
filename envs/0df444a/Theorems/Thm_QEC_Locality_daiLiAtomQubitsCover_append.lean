-- Prove2me | Theorems.Thm_QEC_Locality_daiLiAtomQubitsCover_append
-- name    : QEC.Locality.daiLiAtomQubitsCover_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:50.298575+00:00
-- url     : https://prove2.me/theorems/baf0ab55-46a0-4b73-8df5-99dd67ea4a26
-- title:
--   Locality: dai Li Atom Qubits Cover append
-- statement:
--   The Locality construction uses the dai Li Atom Qubits Cover append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L479-L497
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L479-L497

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

theorem QEC.Locality.daiLiAtomQubitsCover_append
    (embedding : UnitSeparatedEmbedding2D ι) (left right : ℝ)
    (first second : List (ℝ × ℝ)) :
    daiLiAtomQubitsCover embedding left right (first ++ second) =
      daiLiAtomQubitsCover embedding left right first ∪
        daiLiAtomQubitsCover embedding left right second := by sorry
