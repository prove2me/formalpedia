-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_closed_Xstar_vertex_walk
-- name    : QEC.Coding.BDL26BaseGeometricDomain.closed_Xstar_vertex_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T12:36:58.988297+00:00
-- url     : https://prove2.me/theorems/3f376d19-54e3-4be7-9822-1cf38d95cd6f
-- title:
--   BDL26 Base Geometric Domain: closed Xstar vertex walk
-- statement:
--   A precise at-most-two-edge undirected walk in the EXISTING skeleton;
--   no new graph or radius/owner identification is introduced.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18639-L18654
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18639-L18654

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

theorem QEC.Coding.BDL26BaseGeometricDomain.closed_Xstar_vertex_walk (P : TannerSquarePresentation) (x : P.X)
    (v : Vertex P) (hv : xStarVertexMember P x v=true) :
    v=.x x ∨ (tannerSkeleton P).adjacent (.x x) v ∨
      ∃ w : Vertex P, (tannerSkeleton P).adjacent (.x x) w ∧
        (tannerSkeleton P).adjacent w v := by sorry
