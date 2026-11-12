-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_original_joint_law
-- name    : QEC.Coding.BDL26NativeStateRows.original_joint_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:50:58.108616+00:00
-- url     : https://prove2.me/theorems/b5d21a3f-f3e0-40d7-95d7-340b2e1357d4
-- title:
--   BDL26 Native State Rows: original joint law
-- statement:
--   Full original event-labelled joint law, not only the output marginal.
--   The equivalence is internally constructed; no new event order or law occurs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L784-L797
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L784-L797

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_VariableRelabeling_original_joint_law

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
open scoped Classical
open QEC.Coding.ProbabilisticConstruction

theorem QEC.Coding.BDL26NativeStateRows.original_joint_law (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (radius cutoff : ℝ) (hc : cutoff<1) :
    letI (v : Vertex (P S n)) := vertexLaw_probability (P S n) radius hc v
    letI (a : Index S n) := BDL26RandomPerturbation.VariableRelabeling.pulledVertexLaw_probability
      (P S n) radius cutoff hc (decode S n) a
    (tableLaw (BDL26RandomPerturbation.VariableRelabeling.pulledVertexLaw
      (P S n) radius cutoff (decode S n))).map
      (QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decodedObservation
        (decode S n) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))=
      (tableLaw (vertexLaw (P S n) radius cutoff)).map
        (QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.jointObservation
          (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K)) := by sorry
