-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_check401_eq_cyclic_mul_checkOrbit
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.card_check401_eq_cyclic_mul_checkOrbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:31:47.682057+00:00
-- url     : https://prove2.me/theorems/22e54b16-534f-4a93-bd42-595d23f715ed
-- title:
--   LPSQuotient Tanner: card check401 eq cyclic mul check Orbit
-- statement:
--   The actual LPS check set is the free cyclic cover of its check-orbit set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L645-L654
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L645-L654

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.card_check401_eq_cyclic_mul_checkOrbit
    (q : ℕ) [Fact q.Prime] :
    Fintype.card (Check401 q) = q * Fintype.card (CheckOrbit401 q) := by sorry
