-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_subdivisionBoundaryIncidentEdge_original_zero
-- name    : QEC.Coding.BDL26TannerLocalRegularity.subdivisionBoundaryIncidentEdge_original_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:31:50.227918+00:00
-- url     : https://prove2.me/theorems/98dea61b-9303-4fb2-9f99-301c42473776
-- title:
--   BDL26 Tanner Local Regularity: subdivision Boundary Incident Edge original zero
-- statement:
--   On an original boundary vertex tagged at the start of its owned old edge,
--   the subdivision incident-edge selector returns the first segment and endpoint
--   zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L1050-L1073
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L1050-L1073

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26TannerLocalRegularity
open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
universe u

theorem QEC.Coding.BDL26TannerLocalRegularity.subdivisionBoundaryIncidentEdge_original_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV2 P)
    (x : P.X) (S : OddScale) (vertex : XStarBoundaryVertex P x)
    (hzero : (A.xBoundaryIncidentEdge x vertex).1.2 = 0) :
    (subdivisionBoundaryIncidentEdge P A x S
      (subdivisionOriginalBoundaryVertex P x S vertex)).1 =
      (subdivisionOriginalBoundaryEdge P x S
        (A.xBoundaryIncidentEdge x vertex).1.1 ⟨0, S.half_pos⟩, 0) := by sorry
