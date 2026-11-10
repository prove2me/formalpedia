-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_sharedQ_card_le_two
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.sharedQ_card_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:24:55.735366+00:00
-- url     : https://prove2.me/theorems/651e86a5-eba0-4e09-9e94-c024c8d2f4eb
-- title:
--   BDL26 XLocal Connecting Weight: shared Q card le two
-- statement:
--   Regularity bounds the actual shared-Q fibre by the two face corners.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L69-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L69-L79

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_sharedQ_card_le_two

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.sharedQ_card_le_two (P : TannerSquarePresentation)
    (R : TannerSquareCellularRegular P) (x : P.X) (z : P.Z) :
    Fintype.card (SharedQ P.data x z) ≤ 2 := by sorry
