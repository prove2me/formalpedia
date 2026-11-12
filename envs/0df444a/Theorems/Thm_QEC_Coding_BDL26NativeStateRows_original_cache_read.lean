-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_original_cache_read
-- name    : QEC.Coding.BDL26NativeStateRows.original_cache_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:42:44.95532+00:00
-- url     : https://prove2.me/theorems/a1080d70-5514-464e-9f94-a9409abcb821
-- title:
--   BDL26 Native State Rows: original cache read
-- statement:
--   The BDL26 Native State Rows construction uses the original cache read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L722-L730
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L722-L730

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

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

theorem QEC.Coding.BDL26NativeStateRows.original_cache_read (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ)
    (v : Vertex (P S n)) :
    (readQ ((decode S n).symm v)
      (executeQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).value).value=
      (counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) (asTable T) m v,
        T (v,counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) (asTable T) m v)) := by sorry
