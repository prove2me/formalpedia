-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_refresh_original_read
-- name    : QEC.Coding.BDL26NativeSupportMetadata.refresh_original_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:11:40.015816+00:00
-- url     : https://prove2.me/theorems/4cd38e5e-78d3-4ad8-ab69-7c6ad1a71981
-- title:
--   BDL26 Native Support Metadata: refresh original read
-- statement:
--   The BDL26 Native Support Metadata construction uses the refresh original read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L723-L738
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L723-L738

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open N
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeSupportMetadata.refresh_original_read (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (table : BDL26NativeStateRows.Samples (Vertex (P S n)))
    (m : ℕ) (e : Event (P S n) J r) (v : Vertex (P S n)) :
    ((refreshEventQ S n (eventCodes S n J r e) (BDL26NativeStateRows.encodeSamples S n table)
      (BDL26NativeStateRows.originalTrace S n J r lambda K table m)).value.map
      (fun rows => (BDL26NativeStateRows.readQ ((BDL26NativeStateRows.decode S n).symm v) rows).value))=
      some (advance (eventSupport (P S n) J r) e
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable table) m) v,
        table (v,advance (eventSupport (P S n) J r) e
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable table) m) v)) := by sorry
