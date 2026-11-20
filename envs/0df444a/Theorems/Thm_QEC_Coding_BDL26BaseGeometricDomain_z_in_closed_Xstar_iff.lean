-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_z_in_closed_Xstar_iff
-- name    : QEC.Coding.BDL26BaseGeometricDomain.z_in_closed_Xstar_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:05:31.558604+00:00
-- url     : https://prove2.me/theorems/e73a454d-361d-48f2-93f1-634a65418588
-- title:
--   BDL26 Base Geometric Domain: z in closed Xstar iff
-- statement:
--   The closed X-star Z carrier is exactly the actual two-incidence path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18619-L18635
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18619-L18635

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare

set_option autoImplicit false
open QEC.Coding.BDL26FiniteTannerSquare

theorem QEC.Coding.BDL26BaseGeometricDomain.z_in_closed_Xstar_iff (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :
    xStarVertexMember P x (.z z)=true ↔
      ∃ q : P.Q, P.xq x q=true ∧ P.qz q z=true := by sorry
