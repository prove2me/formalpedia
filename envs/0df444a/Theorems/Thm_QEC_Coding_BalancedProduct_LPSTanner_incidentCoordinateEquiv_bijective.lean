-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_incidentCoordinateEquiv_bijective
-- name    : QEC.Coding.BalancedProduct.LPSTanner.incidentCoordinateEquiv_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:25:05.7682+00:00
-- url     : https://prove2.me/theorems/6a05ed6e-31c1-4250-90b3-d977b945f726
-- title:
--   LPSTanner: incident Coordinate Equiv bijective
-- statement:
--   The LPSTanner construction uses the incident Coordinate Equiv bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L162-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean#L162-L168

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph

theorem QEC.Coding.BalancedProduct.LPSTanner.incidentCoordinateEquiv_bijective
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    Function.Bijective (incidentCoordinateEquiv q hq40 hq g) := by sorry
