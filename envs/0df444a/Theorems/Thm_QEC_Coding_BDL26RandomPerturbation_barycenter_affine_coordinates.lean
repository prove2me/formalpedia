-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_barycenter_affine_coordinates
-- name    : QEC.Coding.BDL26RandomPerturbation.barycenter_affine_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:10:11.658205+00:00
-- url     : https://prove2.me/theorems/fee0fb48-161e-4953-9790-3633e4a6e627
-- title:
--   BDL26 Random Perturbation: barycenter affine coordinates
-- statement:
--   The BDL26 Random Perturbation construction uses the barycenter affine coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleMinimum.lean#L42-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleMinimum.lean#L42-L53

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem QEC.Coding.BDL26RandomPerturbation.barycenter_affine_coordinates (a : Fin 3 → Space)
    (w : stdSimplex ℝ (Fin 3)) :
    barycenterMap a w = a 0+w.val 1 • (a 1-a 0)+w.val 2 • (a 2-a 0) := by sorry
