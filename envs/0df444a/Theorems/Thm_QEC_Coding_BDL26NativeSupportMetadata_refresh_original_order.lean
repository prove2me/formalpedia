-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_refresh_original_order
-- name    : QEC.Coding.BDL26NativeSupportMetadata.refresh_original_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:12:16.40169+00:00
-- url     : https://prove2.me/theorems/76ab12e3-5210-4875-9ff2-7be244b6b3df
-- title:
--   BDL26 Native Support Metadata: refresh original order
-- statement:
--   The BDL26 Native Support Metadata construction uses the refresh original order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L740-L747
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L740-L747

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
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

theorem QEC.Coding.BDL26NativeSupportMetadata.refresh_original_order (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (table : BDL26NativeStateRows.Samples (Vertex (P S n)))
    (m : ℕ) (e : Event (P S n) J r) :
    ((refreshEventQ S n (eventCodes S n J r e) (BDL26NativeStateRows.encodeSamples S n table)
      (BDL26NativeStateRows.originalTrace S n J r lambda K table m)).value.map
      (List.map Prod.fst))=some (BDL26NativeStateRows.indices (BDL26NativeStateRows.count S n)) := by sorry
