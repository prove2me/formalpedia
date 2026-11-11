-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_refresh_original
-- name    : QEC.Coding.BDL26NativeSupportMetadata.refresh_original
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:53:24.535726+00:00
-- url     : https://prove2.me/theorems/df5f6e0d-250e-4c2b-916c-aa08dff20d20
-- title:
--   BDL26 Native Support Metadata: refresh original
-- statement:
--   The unchanged original event increments precisely its original support;
--   all native cache rows are constructed inside refreshEventQ. The old selected
--   trace remains the same explicitly external ingress used by the parent API.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L706-L721
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L706-L721

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

theorem QEC.Coding.BDL26NativeSupportMetadata.refresh_original (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (table : BDL26NativeStateRows.Samples (Vertex (P S n)))
    (m : ℕ) (e : Event (P S n) J r) :
    (refreshEventQ S n (eventCodes S n J r e) (BDL26NativeStateRows.encodeSamples S n table)
      (BDL26NativeStateRows.originalTrace S n J r lambda K table m)).value=some
      (BDL26NativeStateRows.rowsFor (BDL26NativeStateRows.indices (BDL26NativeStateRows.count S n))
        (BDL26NativeStateRows.encodeSamples S n table)
        (fun a => advance (eventSupport (P S n) J r) e
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable table) m)
          (BDL26NativeStateRows.decode S n a))) := by sorry
