-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecutionCost_native_nontermination_cost_default
-- name    : QEC.Coding.BDL26NativeGeometricExecutionCost.native_nontermination_cost_default
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:58:58.890354+00:00
-- url     : https://prove2.me/theorems/03c65a02-65b2-49cc-9792-777878d55c08
-- title:
--   BDL26 Native Geometric Execution Cost: native nontermination cost default
-- statement:
--   Exceptional nontermination keeps the original output default, with infinite
--   paid execution cost rather than the zero mathematical default clock.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L829-L836
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L829-L836

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_StrictSlackMoments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricExecutionCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26NativeGeometricExecutionCost.native_nontermination_cost_default (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : OriginalTable S n)
    (h : ¬NativeHalts S n J hr lambda K (SR.encodeSamples S n T)) :
    nativeOperationCost S n J hr lambda K (SR.encodeSamples S n T)=∞ ∧
    returned S n J hr lambda K (SR.encodeSamples S n T)=(fun v => T (v,0)) := by sorry
