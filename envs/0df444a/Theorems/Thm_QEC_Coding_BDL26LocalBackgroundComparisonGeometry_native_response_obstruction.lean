-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonGeometry_native_response_obstruction
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonGeometry.native_response_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:39:23.351408+00:00
-- url     : https://prove2.me/theorems/a69599cb-9178-45d6-b047-1fd01dc5246a
-- title:
--   BDL26 Local Background Comparison Geometry: native response obstruction
-- statement:
--   One genuine bad background/flip works for EVERY successful native history
--   and EVERY support-contained restricted word at every centre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonGeometry.lean#L45-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonGeometry.lean#L45-L75

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonGeometry.native_response_obstruction {L : ℝ} (p : GeometricParameters L)
    (large : 33 ≤ (perturbationOddScale p).ell) (R : ℝ) :
    ∃ (g : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))
      (q : Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R))),
      ballBudget p.t R < HammingWeight g ∧ g ≠ 0 ∧
      canonicalBasisWord (F:=BDL26Field) q ≠
        (0 : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R))) ∧
      BDL26AllDepthBottomComparisonStability.residual (perturbationOddScale p) (budgetDepth (ballBudget p.t R))
        (perturbTop (perturbationOddScale p) (budgetDepth (ballBudget p.t R))
          (BDL26NonzeroBackgroundComparisonStability.zeroInput (perturbationOddScale p) (budgetDepth (ballBudget p.t R))) g)
        (canonicalBasisWord (F:=BDL26Field) q) ∉
          boundaries (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) ∧
      ∀ (z : BDL26NativeFiniteComposition.Experiment p (responseLevel p.t R)),
        z ∈ BDL26NativeFiniteComposition.finiteSuccess p (responseLevel p.t R) →
        ∀ (center : Space) (A : Finset (Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))),
          (∀ u ∈ hammingSupport (backgroundRestriction (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g A),
            dist (BDL26NativeFiniteComposition.history p (responseLevel p.t R) z
              (Fin.last (responseLevel p.t R)) (.q u)) center ≤ R) →
          ChangesDefect (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g q A := by sorry
