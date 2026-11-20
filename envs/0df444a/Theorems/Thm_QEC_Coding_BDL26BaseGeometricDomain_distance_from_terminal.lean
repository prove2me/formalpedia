-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_distance_from_terminal
-- name    : QEC.Coding.BDL26BaseGeometricDomain.distance_from_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T12:39:38.573998+00:00
-- url     : https://prove2.me/theorems/41c1d70f-4e7e-49c5-8bdf-65048e5526d8
-- title:
--   BDL26 Base Geometric Domain: distance from terminal
-- statement:
--   The ORIGINAL bounded directed-distance search from a terminal vertex
--   returns zero exactly at that vertex, and infinity elsewhere. The induction
--   uses the original search; it does not introduce another graph or search.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18659-L18678
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18659-L18678

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

theorem QEC.Coding.BDL26BaseGeometricDomain.distance_from_terminal {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (u : V) (hu : ∀ w, G.edge u w=false) (v : V) :
    G.distance u v=(if u=v then 0 else ⊤) := by sorry
