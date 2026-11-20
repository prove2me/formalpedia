-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_q_in_closed_Xstar_iff
-- name    : QEC.Coding.BDL26BaseGeometricDomain.q_in_closed_Xstar_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T12:37:53.283496+00:00
-- url     : https://prove2.me/theorems/f2884b2e-67ba-4f4f-b14b-3590292423e9
-- title:
--   BDL26 Base Geometric Domain: q in closed Xstar iff
-- statement:
--   The existing closed X-star Q carrier is characterized by a genuine shared
--   Q corner, with both incidences derived from the presented square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18584-L18616
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18584-L18616

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint
set_option autoImplicit false
noncomputable section
noncomputable section
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BaseGeometricDomain
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open scoped Classical

theorem QEC.Coding.BDL26BaseGeometricDomain.q_in_closed_Xstar_iff (P : TannerSquarePresentation) (x : P.X) (q : P.Q) :
    xStarVertexMember P x (.q q)=true ↔
      ∃ z : P.Z, P.xq x q=true ∧ P.qz q z=true := by sorry
