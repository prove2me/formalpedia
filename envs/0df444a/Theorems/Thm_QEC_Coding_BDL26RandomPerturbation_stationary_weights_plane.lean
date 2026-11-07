-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stationary_weights_plane
-- name    : QEC.Coding.BDL26RandomPerturbation.stationary_weights_plane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:20:56.664236+00:00
-- url     : https://prove2.me/theorems/6b5b24a5-964e-4065-bc8f-2459f7f7c059
-- title:
--   BDL26 Random Perturbation: stationary weights plane
-- statement:
--   The BDL26 Random Perturbation construction uses the stationary weights plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleMinimum.lean#L104-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleMinimum.lean#L104-L125

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.stationary_weights_plane (a : Fin 3 → Space) (z : Space)
    (w : stdSimplex ℝ (Fin 3))
    (hi : ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) = 0)
    (hdet : gramDet (a 1-a 0) (a 2-a 0) ≠ 0) :
    w.val 1 = planeU (a 1-a 0) (a 2-a 0) (z-a 0) ∧
      w.val 2 = planeV (a 1-a 0) (a 2-a 0) (z-a 0) := by sorry
