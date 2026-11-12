-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_expected_steps_explicit_finite
-- name    : QEC.Coding.BDL26KeyedGeometricExecution.expected_steps_explicit_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:04:17.869891+00:00
-- url     : https://prove2.me/theorems/33737595-5bc4-4762-86f2-df2bd354adc1
-- title:
--   BDL26 Keyed Geometric Execution: expected steps explicit finite
-- statement:
--   The BDL26 Keyed Geometric Execution construction uses the expected steps explicit finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricExecution.lean#L182-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricExecution.lean#L182-L197

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometricExecution
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26KeyedGeometricExecution.expected_steps_explicit_finite (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    (∫⁻ T, totalSteps (keySupport P k hk J (anchorRadius p.m))
      (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
      ∂tableMeasure P p) ≤
      ENNReal.ofReal ((Fintype.card (Triangle P) : ℝ)^4 *
        (lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)))) ∧
    ENNReal.ofReal ((Fintype.card (Triangle P) : ℝ)^4 *
        (lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)))) < ∞ := by sorry
