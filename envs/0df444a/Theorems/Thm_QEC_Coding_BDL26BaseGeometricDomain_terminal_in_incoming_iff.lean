-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_terminal_in_incoming_iff
-- name    : QEC.Coding.BDL26BaseGeometricDomain.terminal_in_incoming_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T12:41:55.887964+00:00
-- url     : https://prove2.me/theorems/d5e6b3a7-28c9-48b4-b557-c10c0e04861c
-- title:
--   BDL26 Base Geometric Domain: terminal in incoming iff
-- statement:
--   A terminal source belongs to an ORIGINAL incoming region of any finite
--   radius exactly when it is the region centre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18682-L18689
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18682-L18689

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

theorem QEC.Coding.BDL26BaseGeometricDomain.terminal_in_incoming_iff {V : Type} [Fintype V] [DecidableEq V]
    (G : DirectedGraph V) (u : V) (hu : ∀ w, G.edge u w=false)
    (v : V) (radius : Nat) :
    u ∈ LocalRegion.directedNeighborhood G v radius ↔ u=v := by sorry
