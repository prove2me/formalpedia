-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonGeometry_support_inside_of_mask_inside
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonGeometry.support_inside_of_mask_inside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:38:43.97358+00:00
-- url     : https://prove2.me/theorems/2274554e-4ad7-4e65-b2c0-9354cefe7d5c
-- title:
--   BDL26 Local Background Comparison Geometry: support inside of mask inside
-- statement:
--   The mask-contained version permits arbitrary adaptive masks and centres.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonGeometry.lean#L78-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonGeometry.lean#L78-L88

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalBackgroundComparisonResponse BDL26LocalBackgroundComparisonDepth
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26LocalBackgroundComparisonGeometry.support_inside_of_mask_inside (S : OddScale) (n : Nat) (g : W S n)
    (A : Finset (Q S n)) (J : Vertex (state S (n+2)).presentation → Space)
    (center : Space) (R : ℝ) (inside : ∀ q ∈ A, dist (J (.q q)) center ≤ R) :
    ∀ q ∈ hammingSupport (backgroundRestriction S n g A), dist (J (.q q)) center ≤ R := by sorry
