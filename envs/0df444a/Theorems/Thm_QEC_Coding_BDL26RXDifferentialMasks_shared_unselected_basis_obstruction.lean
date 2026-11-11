-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_shared_unselected_basis_obstruction
-- name    : QEC.Coding.BDL26RXDifferentialMasks.shared_unselected_basis_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:01:11.502175+00:00
-- url     : https://prove2.me/theorems/99abf545-6a41-46d2-86b1-f2fe42da20e7
-- title:
--   BDL26 RXDifferential Masks: shared unselected basis obstruction
-- statement:
--   A shared Z incidence gives an explicit BASIS input violating the naive
--   forward mask whenever its other incident Q is omitted. No cancellation or
--   single-word implication is used to infer the all-input criterion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L290-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L290-L307

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.shared_unselected_basis_obstruction (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (q r : (state S i.val).presentation.Q) (z : (state S i.val).presentation.Z)
    (hq : q ∈ A) (hr : r ∉ A)
    (hqz : (state S i.val).presentation.qz q z = true)
    (hrz : (state S i.val).presentation.qz r z = true) :
    maskWord (nativeRegion S depth i h A)
        (nativeDifferential S depth i (canonicalBasisWord r)) ≠
      nativeDifferential S depth i (maskWord A (canonicalBasisWord r)) := by sorry
