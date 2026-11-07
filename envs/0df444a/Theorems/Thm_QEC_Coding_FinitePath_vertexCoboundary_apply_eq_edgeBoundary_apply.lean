-- Prove2me | Theorems.Thm_QEC_Coding_FinitePath_vertexCoboundary_apply_eq_edgeBoundary_apply
-- name    : QEC.Coding.FinitePath.vertexCoboundary_apply_eq_edgeBoundary_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:10:03.207657+00:00
-- url     : https://prove2.me/theorems/64a9e5c5-cbd7-4bcf-a74b-3d8cfc186d25
-- title:
--   Finite Path: vertex Coboundary apply eq edge Boundary apply
-- statement:
--   Vertex-edge incidence is symmetric between the path boundary and
--   coboundary descriptions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean#L98-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean#L98-L119

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F] [DecidableEq F]

theorem QEC.Coding.FinitePath.vertexCoboundary_apply_eq_edgeBoundary_apply
    {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    vertexCoboundary (F := F) i j = edgeBoundary (F := F) j i := by sorry
