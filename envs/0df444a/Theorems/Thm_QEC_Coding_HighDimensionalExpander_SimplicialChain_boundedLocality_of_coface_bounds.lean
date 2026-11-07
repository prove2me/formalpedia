-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SimplicialChain_boundedLocality_of_coface_bounds
-- name    : QEC.Coding.HighDimensionalExpander.SimplicialChain.boundedLocality_of_coface_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:52:55.786001+00:00
-- url     : https://prove2.me/theorems/68a4385e-709e-44d7-9276-a05ec72f2750
-- title:
--   Simplicial Chain: bounded Locality of coface bounds
-- statement:
--   A genuine uniform coface bound gives qLDPC locality for the extracted
--   simplicial chain complex.  Downward incidences are counted exactly from the
--   face cardinalities; only upward degrees are hypotheses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L395-L424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L395-L424

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

theorem QEC.Coding.HighDimensionalExpander.SimplicialChain.boundedLocality_of_coface_bounds
    (p B : Nat) (hp : 1 ≤ p)
    (hLower : ∀ σ : Face K p, (cofaces K p σ).card ≤ B)
    (hMiddle : ∀ τ : Face K (p + 1),
      (cofaces K (p + 1) τ).card ≤ B) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplexAt K p)).localityProfile
      (max (max B (p + 2)) (p + 1 + B)) := by sorry
