-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_lsvQuotientComplex_faces_incidence_formula
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_faces_incidence_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:36:29.167062+00:00
-- url     : https://prove2.me/theorems/14f8e620-75d7-4c64-be49-c66869dc1700
-- title:
--   Cartwright Steger: card lsv Quotient Complex faces incidence formula
-- statement:
--   Exact face-incidence formula for every selected finite LSV quotient,
--   with the global vertex factor written as the genuine lattice congruence
--   quotient.  This covers every face degree, not only the top-dimensional
--   chambers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1450-L1477
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1450-L1477

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_lsvQuotientComplex_faces_incidence_formula
    (P : BasePrime) (r : Rank) (level p : Nat) :
    p * Fintype.card
        (SimplicialChain.Face (lsvQuotientComplex P r level) p) =
      Nat.card
          (OrderSplitCartwrightStegerLattice P r ⧸
            OrderSplitCartwrightStegerCongruenceSubgroup P r level) *
        Fintype.card
          {σ : SimplicialChain.Face
              (lsvQuotientComplex P r level) p //
            1 ∈ σ.vertices} := by sorry
