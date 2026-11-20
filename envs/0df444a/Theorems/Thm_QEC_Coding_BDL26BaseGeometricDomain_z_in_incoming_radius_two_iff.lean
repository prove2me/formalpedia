-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_z_in_incoming_radius_two_iff
-- name    : QEC.Coding.BDL26BaseGeometricDomain.z_in_incoming_radius_two_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T12:38:47.872326+00:00
-- url     : https://prove2.me/theorems/7051eb64-fb1c-46e5-b2cd-99acaa84a628
-- title:
--   BDL26 Base Geometric Domain: z in incoming radius two iff
-- statement:
--   A Z source has no directed outgoing edges. Incoming neighborhoods are
--   therefore fundamentally different from the undirected balls above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18704-L18708
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18704-L18708

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

theorem QEC.Coding.BDL26BaseGeometricDomain.z_in_incoming_radius_two_iff (S : OddScale) (n : Nat)
    (z : (state S n).presentation.Z) (v : Vertex (state S n).presentation) :
    Vertex.z z ∈ LocalRegion.directedNeighborhood
      (tannerLevel (state S n).presentation).graph v 2 ↔ Vertex.z z=v := by sorry
