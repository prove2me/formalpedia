-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_weightedNeighborSum_eq_degree_mul_sum
-- name    : QEC.Coding.SmallSetExpansion.sum_weightedNeighborSum_eq_degree_mul_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:37:54.561977+00:00
-- url     : https://prove2.me/theorems/5d8da333-557e-46c9-b131-a95e8ba5f99c
-- title:
--   Small Set Expansion: sum weighted Neighbor Sum eq degree mul sum
-- statement:
--   Symmetry and regularity make adjacency preserve the mean-zero subspace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L370-L398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L370-L398

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.sum_weightedNeighborSum_eq_degree_mul_sum
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (g : V → ℝ) :
    ∑ v, weightedNeighborSum M g v = degree * ∑ v, g v := by sorry
