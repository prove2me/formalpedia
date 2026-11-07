-- Prove2me | Theorems.Thm_QEC_Coding_FinitePath_HammingWeight_edgeBoundary_le_two
-- name    : QEC.Coding.FinitePath.HammingWeight_edgeBoundary_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:40:25.547353+00:00
-- url     : https://prove2.me/theorems/bdd3366d-9354-4a42-b13c-0731021c66af
-- title:
--   Finite Path: Hamming Weight edge Boundary le two
-- statement:
--   Every path edge has exactly two candidate endpoints, hence weight at most
--   two over any field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean#L201-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean#L201-L207

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F]

theorem QEC.Coding.FinitePath.HammingWeight_edgeBoundary_le_two {n : Nat} (j : Fin n) :
    HammingWeight (edgeBoundary (F := F) j) ≤ 2 := by sorry
