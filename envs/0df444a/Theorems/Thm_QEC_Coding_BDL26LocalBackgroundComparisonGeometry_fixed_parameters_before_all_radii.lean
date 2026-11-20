-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonGeometry_fixed_parameters_before_all_radii
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonGeometry.fixed_parameters_before_all_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:38:11.19191+00:00
-- url     : https://prove2.me/theorems/6676204b-05b2-4a49-927c-c1fd433d8c5f
-- title:
--   BDL26 Local Background Comparison Geometry: fixed parameters before all radii
-- statement:
--   One legal numerical choice precedes every radius and every resulting depth.
--   Existence of the original native experiment and its geometry is proved, not assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonGeometry.lean#L111-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonGeometry.lean#L111-L125

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonGeometry.fixed_parameters_before_all_radii (L : ℝ) :
    ∃ p : GeometricParameters L, 33 ≤ (perturbationOddScale p).ell ∧
      ∀ R : ℝ,
    ∃ (g : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))
      (q : Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R))),
      g ≠ 0 ∧ canonicalBasisWord (F:=BDL26Field) q ≠
        (0 : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R))) ∧
      ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (responseLevel p.t R),
        ∀ (center : Space) (A : Finset (Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))),
          (∀ u ∈ hammingSupport (backgroundRestriction (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g A),
            dist (BDL26NativeFiniteComposition.history p (responseLevel p.t R) z
              (Fin.last (responseLevel p.t R)) (.q u)) center ≤ R) →
          ChangesDefect (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g q A := by sorry
