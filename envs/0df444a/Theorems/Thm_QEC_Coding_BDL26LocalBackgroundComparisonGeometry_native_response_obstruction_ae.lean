-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonGeometry_native_response_obstruction_ae
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonGeometry.native_response_obstruction_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:39:49.990217+00:00
-- url     : https://prove2.me/theorems/a190021d-41ef-4c89-a566-b365bdc78022
-- title:
--   BDL26 Local Background Comparison Geometry: native response obstruction ae
-- statement:
--   The same deterministic background/flip is chosen before the almost-sure
--   history quantifier; no uncountable intersection of AE events is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonGeometry.lean#L92-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonGeometry.lean#L92-L107

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonGeometry.native_response_obstruction_ae {L : ℝ} (p : GeometricParameters L)
    (large : 33 ≤ (perturbationOddScale p).ell) (R : ℝ) :
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
