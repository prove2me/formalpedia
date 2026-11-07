-- Prove2me | Theorems.Thm_QEC_Coding_FinitePath_transpose_boundary_single
-- name    : QEC.Coding.FinitePath.transpose_boundary_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:17:12.437105+00:00
-- url     : https://prove2.me/theorems/5090b048-adce-41ff-b254-80becf26034d
-- title:
--   Finite Path: transpose boundary single
-- statement:
--   The transpose row of the path boundary is exactly the endpoint boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean#L147-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean#L147-L163

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [DecidableEq F]

theorem QEC.Coding.FinitePath.transpose_boundary_single {n : Nat} (j : Fin n) :
    wordLinearMapTranspose (boundary (F := F)) (Pi.single j 1) =
      edgeBoundary (F := F) j := by sorry
