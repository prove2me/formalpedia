-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:43:43.043454+00:00
-- url     : https://prove2.me/theorems/f70fea14-7207-4f01-b01e-f999beee094c
-- title:
--   Cartwright Steger: order Unit To Building PGL mem compact Cyclic Subgroup of mem maximal Compact
-- statement:
--   Every projectively compact arithmetic-order unit has image in the
--   explicit compact cyclic subgroup.  The proof constructs its normalized unit,
--   both integral matrices, and the corresponding skew Laurent unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L307-L324
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L307-L324

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    orderUnitToBuildingPGL P r u ∈
      BuildingCompactCyclicSubgroup P r := by sorry
