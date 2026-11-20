-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveC2QEndpoint_exists_original_oldX_all_odd_first_zero_chi_one
-- name    : QEC.Coding.BDL26RXPrimitiveC2QEndpoint.exists_original_oldX_all_odd_first_zero_chi_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T12:41:45.563658+00:00
-- url     : https://prove2.me/theorems/5c54c94a-019b-4717-9a3a-88baa8f1d881
-- title:
--   BDL26 RXPrimitive C2 QEndpoint: exists original old X all odd first zero chi one
-- statement:
--   For every admissible odd scale, at N=1 the original model has one legal
--   background and one physical old-X error in Physical S 3 with exact parser class,
--   FIRST readout zero, and actual logical defect one. The same background and error
--   occur in all three conclusions. This is the single RX suffix from C3 to C2;
--   the old-X edge chart belongs to state S 2. No arbitrary-depth or lifetime claim
--   is made. The public statement quantifies the owner with no private coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18360-L18373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18360-L18373

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint
set_option autoImplicit false
noncomputable section
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveC2QEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RXPhysicalCoordinateTrace
open scoped Classical

theorem QEC.Coding.BDL26RXPrimitiveC2QEndpoint.exists_original_oldX_all_odd_first_zero_chi_one (S : OddScale) :
    ∃ x : (state S 1).presentation.X,
      ∃ outer : BDL26FiniteTannerSquare.Two,
      ∃ u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 1,
      ∃ edge : DoubleCylinderEdge (state S 2).presentation
          (oldXOwner S 1 (by decide) x outer) S,
        parse S 1 (oldXPhysical S 1 (by decide) x outer edge)=
          Leaf.primitive (Primitive.oldX 1 (by decide) x outer edge) ∧
        firstReadout S 1 u=0 ∧
          BDL26LogicalDefectProtection.chiX S 1 u
            (oldXPhysical S 1 (by decide) x outer edge)=1 := by sorry
