-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_scanKey_length
-- name    : QEC.Coding.BDL26KeyedGeometricExecution.scanKey_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:45:08.325951+00:00
-- url     : https://prove2.me/theorems/fa3ef32d-6e9c-4fe8-b6ad-184aef5f82b9
-- title:
--   BDL26 Keyed Geometric Execution: scan Key length
-- statement:
--   The BDL26 Keyed Geometric Execution construction uses the scan Key length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricExecution.lean#L35-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricExecution.lean#L35-L39

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

theorem QEC.Coding.BDL26KeyedGeometricExecution.scanKey_length (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ)
    (e : KeyEvent P k hk J r) : (scanKey P k hk J r e).length = 4 := by sorry
