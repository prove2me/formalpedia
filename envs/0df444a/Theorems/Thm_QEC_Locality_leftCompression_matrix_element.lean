-- Prove2me | Theorems.Thm_QEC_Locality_leftCompression_matrix_element
-- name    : QEC.Locality.leftCompression_matrix_element
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:38.688786+00:00
-- url     : https://prove2.me/theorems/6048a84c-df1d-4045-aba1-362cb2989437
-- title:
--   Locality: left Compression matrix element
-- statement:
--   The Locality construction uses the left Compression matrix element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L818-L832
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L818-L832

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.leftCompression_matrix_element (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem) (k l : S.complementSystem) :
    inner Complex l (leftCompression S A k) =
      ∑ h : Qubit.Bitstring S.SelectedCoordinates,
        inner Complex (ket h ⊗ₜ[Complex] l) (A (ket h ⊗ₜ[Complex] k)) := by sorry
