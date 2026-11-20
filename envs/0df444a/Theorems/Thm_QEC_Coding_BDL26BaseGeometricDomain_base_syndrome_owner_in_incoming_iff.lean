-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BaseGeometricDomain_base_syndrome_owner_in_incoming_iff
-- name    : QEC.Coding.BDL26BaseGeometricDomain.base_syndrome_owner_in_incoming_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T12:39:59.982179+00:00
-- url     : https://prove2.me/theorems/a54353b1-689f-4f4c-b9ef-1f9f0672b577
-- title:
--   BDL26 Base Geometric Domain: base syndrome owner in incoming iff
-- statement:
--   EVERY original canonical base-syndrome owner is a Z vertex. Thus its
--   incoming-region membership is equality with the centre, independent of any
--   support classification or choice of two surviving syndrome checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18713-L18725
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveC2QEndpoint.lean#L18713-L18725

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

theorem QEC.Coding.BDL26BaseGeometricDomain.base_syndrome_owner_in_incoming_iff (S : OddScale) (n : Nat)
    (p : BDL26IndexedDecoder.FamilyZ S (n+2)
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n)))
    (center : GraphVertex S 2) (radius : Nat) :
    BDL26CanonicalHistoryMarks.baseSyndromeOwner S n p ∈
      LocalRegion.directedNeighborhood (level S 2).graph center radius ↔
        BDL26CanonicalHistoryMarks.baseSyndromeOwner S n p=center := by sorry
