-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LogicalQubitPreservation_logicalEquiv_eq_iff_boundary
-- name    : QEC.Coding.BDL26LogicalQubitPreservation.logicalEquiv_eq_iff_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:48:44.687009+00:00
-- url     : https://prove2.me/theorems/d5586e53-c822-4ea3-9f04-1b610acf6ee9
-- title:
--   BDL26 Logical Qubit Preservation: logical Equiv eq iff boundary
-- statement:
--   The BDL26 Logical Qubit Preservation construction uses the logical Equiv eq iff boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L96-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean#L96-L105

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26LogicalQubitPreservation.logicalEquiv_eq_iff_boundary (S : OddScale) (n : Nat)
    (u v : DualRepresentative S n) :
    logicalEquiv S n (logicalClass S n u) = logicalEquiv S n (logicalClass S n v) ↔
      ∃ f : Word Field (state S n).presentation.X,
        tannerCoboundary0 (state S n).presentation f = fun q => u.1 q - v.1 q := by sorry
