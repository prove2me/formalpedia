-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_original_cache_cost
-- name    : QEC.Coding.BDL26NativeStateRows.original_cache_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:50:13.758257+00:00
-- url     : https://prove2.me/theorems/b67797b8-1062-4439-ad75-72fd59bdb422
-- title:
--   BDL26 Native State Rows: original cache cost
-- statement:
--   Polynomial cache overhead on original finite prefixes. Construction of the
--   selected event/rank metadata remains external; the full cache work is paid.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L708-L720
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L708-L720

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
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

theorem QEC.Coding.BDL26NativeStateRows.original_cache_cost (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ) :
    (executeQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).operations≤
      (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
        2*(count S n)^2+12*count S n+6+2*m+35*count S n*m ∧
    (executeQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).allocations≤
      (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
        (count S n)^2+2*count S n+2+2*count S n*m := by sorry
