-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SimplicialChain_cosystoleAtLeast_iff_middleCohomologyDistanceAtLeast
-- name    : QEC.Coding.HighDimensionalExpander.SimplicialChain.cosystoleAtLeast_iff_middleCohomologyDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:52:53.356817+00:00
-- url     : https://prove2.me/theorems/eab5063b-2618-4db3-996e-2644b8fd1bd3
-- title:
--   Simplicial Chain: cosystole At Least iff middle Cohomology Distance At Least
-- statement:
--   The Simplicial Chain construction uses the cosystole At Least iff middle Cohomology Distance At Least property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L207-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L207-L211

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

theorem QEC.Coding.HighDimensionalExpander.SimplicialChain.cosystoleAtLeast_iff_middleCohomologyDistanceAtLeast
    (p d : Nat) :
    CosystoleAtLeast K p d ↔
      MiddleCohomologyDistanceAtLeast (chainComplexAt K p) d := by sorry
