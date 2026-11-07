-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_flipSupport_binarySupport_eq_add
-- name    : QEC.Coding.PauliSymplectic.flipSupport_binarySupport_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:32.768056+00:00
-- url     : https://prove2.me/theorems/bbe0984e-55b6-4449-a02f-449ac63ff0b4
-- title:
--   Pauli Symplectic: flip Support binary Support eq add
-- statement:
--   Flipping the support of a binary word is its literal additive translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/BasisAction.lean#L26-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/BasisAction.lean#L26-L30

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PauliSymplectic
open Semantics
universe u
variable {J : Type u} [Fintype J] [DecidableEq J]

theorem QEC.Coding.PauliSymplectic.flipSupport_binarySupport_eq_add (x y : Word (ZMod 2) J) :
    Qubit.flipSupport (binarySupport x) y = y + x := by sorry
