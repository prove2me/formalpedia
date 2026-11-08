-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_subdivisionBoundaryIncidentEdge_original_one
-- name    : QEC.Coding.BDL26TannerLocalRegularity.subdivisionBoundaryIncidentEdge_original_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:32:18.821077+00:00
-- url     : https://prove2.me/theorems/52957892-0511-487e-8ab8-59f8f9ac3921
-- title:
--   BDL26 Tanner Local Regularity: subdivision Boundary Incident Edge original one
-- statement:
--   On an original boundary vertex tagged at the end of its owned old edge,
--   the subdivision incident-edge selector returns the last segment and endpoint
--   one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L1078-L1103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L1078-L1103

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

theorem QEC.Coding.BDL26TannerLocalRegularity.subdivisionBoundaryIncidentEdge_original_one
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV2 P)
    (x : P.X) (S : OddScale) (vertex : XStarBoundaryVertex P x)
    (hone : (A.xBoundaryIncidentEdge x vertex).1.2 = 1) :
    (subdivisionBoundaryIncidentEdge P A x S
      (subdivisionOriginalBoundaryVertex P x S vertex)).1 =
      (subdivisionOriginalBoundaryEdge P x S
        (A.xBoundaryIncidentEdge x vertex).1.1
          ⟨S.half - 1, by have := S.half_pos; omega⟩, 1) := by sorry
