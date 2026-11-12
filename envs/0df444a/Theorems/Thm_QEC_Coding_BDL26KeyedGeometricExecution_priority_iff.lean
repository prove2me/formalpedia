-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_priority_iff
-- name    : QEC.Coding.BDL26KeyedGeometricExecution.priority_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:02:25.86701+00:00
-- url     : https://prove2.me/theorems/b1ad44ef-fe74-4da4-868a-11326cb051f1
-- title:
--   BDL26 Keyed Geometric Execution: priority iff
-- statement:
--   The BDL26 Keyed Geometric Execution construction uses the priority iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricExecution.lean#L74-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricExecution.lean#L74-L78

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

theorem QEC.Coding.BDL26KeyedGeometricExecution.priority_iff (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ)
    (e f : KeyEvent P k hk J r) :
    (keyExecutionOrder P k hk J r).toLE.le e f ↔
      scanKey P k hk J r e ≤ scanKey P k hk J r f := by sorry
