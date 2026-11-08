-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_tannerBoundary_eq_sum_tannerCoefficient
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.tannerBoundary_eq_sum_tannerCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:34:58.398578+00:00
-- url     : https://prove2.me/theorems/57332cd2-038e-4155-ae0b-baf0c041882b
-- title:
--   LPSQuotient Tanner: tanner Boundary eq sum tanner Coefficient
-- statement:
--   Every value of the concrete Tanner linear map is the sum of its basis
--   coefficients against the input word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L417-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L417-L439

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.tannerBoundary_eq_sum_tannerCoefficient
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) (c : Check401 q) :
    tannerBoundary q hq40 hq x c =
      ∑ e : Edge401 q hq, tannerCoefficient q hq40 hq c e * x e := by sorry
