-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_query_original
-- name    : QEC.Coding.BDL26NativeSupportMetadata.query_original
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:51:40.00192+00:00
-- url     : https://prove2.me/theorems/4ea7b9c1-4d3a-42a0-bbd0-9facd153a84c
-- title:
--   BDL26 Native Support Metadata: query original
-- statement:
--   Universal exact original-event support, with no caller success/support
--   certificate. The same original event is encoded internally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L686-L701
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L686-L701

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

theorem QEC.Coding.BDL26NativeSupportMetadata.query_original (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ)
    (e : Event (P S n) J r) :
    ∃U,(queryQ S n (eventCodes S n J r e)).value=some U ∧ U.Nodup ∧ U.length≤12 ∧
      ∀a,a∈U ↔ BDL26NativeStateRows.decode S n a∈eventSupport (P S n) J r e := by sorry
