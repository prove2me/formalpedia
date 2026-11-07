-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_centeredAdjacencyEuclidean_apply_of_sum_eq_zero
-- name    : QEC.Coding.SmallSetExpansion.centeredAdjacencyEuclidean_apply_of_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:37:45.966256+00:00
-- url     : https://prove2.me/theorems/54cf348e-a0f1-4ea9-adab-8173a422d204
-- title:
--   Small Set Expansion: centered Adjacency Euclidean apply of sum eq zero
-- statement:
--   On a mean-zero vector, centered adjacency is ordinary adjacency.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L192-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean#L192-L198

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.centeredAdjacencyEuclidean_apply_of_sum_eq_zero
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (f : EuclideanSpace ℂ V) (hf : (∑ v, f v) = 0) :
    centeredAdjacencyEuclidean M degree f =
      complexAdjacencyEuclidean M f := by sorry
