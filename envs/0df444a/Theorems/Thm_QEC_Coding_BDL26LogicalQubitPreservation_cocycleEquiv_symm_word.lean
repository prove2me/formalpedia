-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_cocycleEquiv_symm_word
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.cocycleEquiv_symm_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:32:38.201905+00:00
-- url     : https://prove2.me/theorems/e300b312-a78b-4938-a7d1-7785f6520120
-- title:
--   BDL26 Logical Qubit Preservation: cocycle Equiv symm word
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the cocycle Equiv symm word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L41-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L41-L46

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.cocycleEquiv_symm_word (S : OddScale) (n : Nat)
    (w : BDL26FiniteCohomology.Cocycle S n) :
    ((cocycleEquiv S n).symm w).1 = w.1 := by sorry
