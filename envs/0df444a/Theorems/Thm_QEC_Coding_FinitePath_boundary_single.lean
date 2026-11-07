-- Prove2me | Theorems.Thm_QEC_Coding_FinitePath_boundary_single
-- name    : QEC.Coding.FinitePath.boundary_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:08:37.461844+00:00
-- url     : https://prove2.me/theorems/99ce32a3-4a07-4880-a12e-da9b55a4c24a
-- title:
--   Finite Path: boundary single
-- statement:
--   The Finite Path construction uses the boundary single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean#L133-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean#L133-L143

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F] [DecidableEq F]

theorem QEC.Coding.FinitePath.boundary_single {n : Nat} (i : Fin (n + 1)) :
    boundary (F := F) (Pi.single i 1) = vertexCoboundary (F := F) i := by sorry
