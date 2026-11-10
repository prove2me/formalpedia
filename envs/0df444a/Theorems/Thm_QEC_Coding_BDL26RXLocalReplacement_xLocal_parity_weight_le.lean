-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_parity_weight_le
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_parity_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:25:23.595849+00:00
-- url     : https://prove2.me/theorems/7f5394b1-5d53-4bfc-800b-f411f2d0e860
-- title:
--   BDL26 RXLocal Replacement: x Local parity weight le
-- statement:
--   A region's binary parity has weight at most the number of its syndromes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L197-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L197-L208

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_parity_weight_le {I : Type} [Fintype I] (f : Word Field I) :
    bitWeight (totalParity f) ≤ HammingWeight f := by sorry
