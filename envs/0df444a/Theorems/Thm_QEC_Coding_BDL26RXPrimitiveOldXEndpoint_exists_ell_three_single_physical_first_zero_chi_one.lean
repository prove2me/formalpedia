-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveOldXEndpoint_exists_ell_three_single_physical_first_zero_chi_one
-- name    : QEC.Coding.BDL26RXPrimitiveOldXEndpoint.exists_ell_three_single_physical_first_zero_chi_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T12:42:13.867515+00:00
-- url     : https://prove2.me/theorems/c34a6c6b-1bca-40c6-b0e9-b6727a030703
-- title:
--   BDL26 RXPrimitive Old XEndpoint: exists ell three single physical first zero chi one
-- statement:
--   A legal ell-three original single-physical-old-X witness with exact parser
--   identity, FIRST readout zero and actual logical defect one. No selector output,
--   NONE branch, defect value or closed non-boundary witness is an assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveOldXEndpoint.lean#L21-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveOldXEndpoint.lean#L21-L37

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveC2QEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveOldXEndpoint
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveOldXEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RXPhysicalCoordinateTrace
open scoped Classical

theorem QEC.Coding.BDL26RXPrimitiveOldXEndpoint.exists_ell_three_single_physical_first_zero_chi_one :
    ∃ S : OddScale,S.ell=3 ∧
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
