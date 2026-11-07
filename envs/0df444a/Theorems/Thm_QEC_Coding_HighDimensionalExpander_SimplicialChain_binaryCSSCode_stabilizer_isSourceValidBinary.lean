-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SimplicialChain_binaryCSSCode_stabilizer_isSourceValidBinary
-- name    : QEC.Coding.HighDimensionalExpander.SimplicialChain.binaryCSSCode_stabilizer_isSourceValidBinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:52:36.67949+00:00
-- url     : https://prove2.me/theorems/290bae9f-a589-4023-b527-143cad6da981
-- title:
--   Simplicial Chain: binary CSSCode stabilizer is Source Valid Binary
-- statement:
--   The CSS stabilizer extracted from the actual simplicial boundaries has
--   the repository's source-valid binary semantics.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L178-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L178-L181

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

theorem QEC.Coding.HighDimensionalExpander.SimplicialChain.binaryCSSCode_stabilizer_isSourceValidBinary (p : Nat) :
    ((chainComplexAt K p).binaryCSSCode).stabilizer.IsSourceValidBinary := by sorry
