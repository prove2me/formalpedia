-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SimplicialChain_systoleAtLeast_iff_middleHomologyDistanceAtLeast
-- name    : QEC.Coding.HighDimensionalExpander.SimplicialChain.systoleAtLeast_iff_middleHomologyDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:52:50.651768+00:00
-- url     : https://prove2.me/theorems/d1442b54-24cf-44fb-a82b-323560a1e8d3
-- title:
--   Simplicial Chain: systole At Least iff middle Homology Distance At Least
-- statement:
--   The Simplicial Chain construction uses the systole At Least iff middle Homology Distance At Least property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L201-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L201-L205

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SimplicialChain
open Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (K : AbstractSimplicialComplex V)

theorem QEC.Coding.HighDimensionalExpander.SimplicialChain.systoleAtLeast_iff_middleHomologyDistanceAtLeast
    (p d : Nat) :
    SystoleAtLeast K p d ↔
      MiddleHomologyDistanceAtLeast (chainComplexAt K p) d := by sorry
