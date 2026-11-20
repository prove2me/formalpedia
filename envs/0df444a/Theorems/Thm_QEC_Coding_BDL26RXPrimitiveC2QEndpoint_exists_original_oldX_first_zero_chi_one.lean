-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveC2QEndpoint_exists_original_oldX_first_zero_chi_one
-- name    : QEC.Coding.BDL26RXPrimitiveC2QEndpoint.exists_original_oldX_first_zero_chi_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T12:41:32.762176+00:00
-- url     : https://prove2.me/theorems/5be71b4a-7fd6-4b74-9b15-3d9ac0454cd5
-- title:
--   BDL26 RXPrimitive C2 QEndpoint: exists original old X first zero chi one
-- statement:
--   At half-scale one the original selector has a legal background and one
--   physical old-X edge with its exact original parser class, FIRST readout zero,
--   and actual logical defect one. Both readouts refer to the same background
--   and physical edge. The owner is quantified so this interface contains no
--   private coordinate name.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L15522-L15535
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L15522-L15535

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

theorem QEC.Coding.BDL26RXPrimitiveC2QEndpoint.exists_original_oldX_first_zero_chi_one (S : OddScale) (hh : S.half=1) :
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
