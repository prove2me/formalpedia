-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_tanner_z_in_incoming_iff
-- name    : QEC.Coding.BDL26BaseGeometricDomain.tanner_z_in_incoming_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:47:24.10406+00:00
-- url     : https://prove2.me/theorems/7b997d5e-3f76-4536-af0b-9a05bb066bb0
-- title:
--   BDL26 Base Geometric Domain: tanner z in incoming iff
-- statement:
--   This applies to every original Tanner presentation, without a bound on
--   its number of vertices: Z vertices are terminal in X-to-Q-to-Z orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18693-L18700
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18693-L18700

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph

set_option autoImplicit false
open QEC.Coding.MultiscaleDecoder QEC.Coding.BDL26FiniteTannerSquare QEC.Coding.BDL26DecodingGraph

theorem QEC.Coding.BDL26BaseGeometricDomain.tanner_z_in_incoming_iff (P : TannerSquarePresentation)
    (z : P.Z) (v : Vertex P) (radius : Nat) :
    Vertex.z z ∈ LocalRegion.directedNeighborhood (tannerLevel P).graph v radius ↔
      Vertex.z z=v := by sorry
