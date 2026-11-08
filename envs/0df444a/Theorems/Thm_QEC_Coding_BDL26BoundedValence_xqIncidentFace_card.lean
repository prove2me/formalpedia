-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedValence_xqIncidentFace_card
-- name    : QEC.Coding.BDL26BoundedValence.xqIncidentFace_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:21:16.812567+00:00
-- url     : https://prove2.me/theorems/ba23829b-77a3-4623-9929-3e1f8ac3b638
-- title:
--   BDL26 Bounded Valence: xq Incident Face card
-- statement:
--   The exact X-Q edge face count is the Q vertex's Z-direction valence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BoundedValence.lean#L107-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BoundedValence.lean#L107-L110

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare

theorem QEC.Coding.BDL26BoundedValence.xqIncidentFace_card (P : TannerSquarePresentation) (e : XQEdge P) :
    Fintype.card (XQIncidentFace P e) = qZDegree P e.1.2 := by sorry
