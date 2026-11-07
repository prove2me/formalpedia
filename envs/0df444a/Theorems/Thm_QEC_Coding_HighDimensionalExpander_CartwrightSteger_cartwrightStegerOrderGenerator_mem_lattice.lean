-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerOrderGenerator_mem_lattice
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderGenerator_mem_lattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:29:21.427673+00:00
-- url     : https://prove2.me/theorems/ba4cab23-9e0f-4681-84db-70d93af70f67
-- title:
--   Cartwright Steger: cartwright Steger Order Generator mem lattice
-- statement:
--   The Cartwright Steger construction uses the cartwright Steger Order Generator mem lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Core.lean#L261-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Core.lean#L261-L269

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderGenerator_mem_lattice
    (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    (QuotientGroup.mk
        (cartwrightStegerOrderGenerator P r
          (constantClassRepresentative P r u)) :
      CartwrightStegerOrderProjectiveGroup P r) ∈
        CartwrightStegerOrderLattice P r := by sorry
