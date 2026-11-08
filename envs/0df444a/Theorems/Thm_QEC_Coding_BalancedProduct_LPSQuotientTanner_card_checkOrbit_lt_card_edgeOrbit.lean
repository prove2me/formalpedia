-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_checkOrbit_lt_card_edgeOrbit
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.card_checkOrbit_lt_card_edgeOrbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:13.856087+00:00
-- url     : https://prove2.me/theorems/f18ecf81-9170-4c5b-913f-37cba4dc630b
-- title:
--   LPSQuotient Tanner: card check Orbit lt card edge Orbit
-- statement:
--   The LPSQuotient Tanner construction uses the card check Orbit lt card edge Orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L846-L872
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L846-L872

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSQuotientTanner
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open Cyclic FreeOrbitCoordinates LPSTanner LPSArithmetic LPSGraph
open PKDistance
set_option maxRecDepth 4000

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.card_checkOrbit_lt_card_edgeOrbit
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (CheckOrbit401 q) < Fintype.card (EdgeOrbit401 q hq) := by sorry
