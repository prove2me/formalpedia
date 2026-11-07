-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SimplicialChain_HammingWeight_transpose_boundary_canonicalBasis_eq_card_cofaces
-- name    : QEC.Coding.HighDimensionalExpander.SimplicialChain.HammingWeight_transpose_boundary_canonicalBasis_eq_card_cofaces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:00:38.621194+00:00
-- url     : https://prove2.me/theorems/e59fa7d5-c7f2-402d-8870-372fe03b25f2
-- title:
--   Simplicial Chain: Hamming Weight transpose boundary canonical Basis eq card cofaces
-- statement:
--   The Simplicial Chain construction uses the Hamming Weight transpose boundary canonical Basis eq card cofaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L319-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L319-L326

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

theorem QEC.Coding.HighDimensionalExpander.SimplicialChain.HammingWeight_transpose_boundary_canonicalBasis_eq_card_cofaces
    (p : Nat) (σ : Face K p) :
    HammingWeight
        (wordLinearMapTranspose (boundary K p)
          (canonicalBasisWord (F := ZMod 2) σ)) =
      (cofaces K p σ).card := by sorry
