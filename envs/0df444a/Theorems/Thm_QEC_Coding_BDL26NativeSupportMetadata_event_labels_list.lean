-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_event_labels_list
-- name    : QEC.Coding.BDL26NativeSupportMetadata.event_labels_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:49:08.904944+00:00
-- url     : https://prove2.me/theorems/d0f7e20e-fb3d-4dde-a4cf-255526843397
-- title:
--   BDL26 Native Support Metadata: event labels list
-- statement:
--   The BDL26 Native Support Metadata construction uses the event labels list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L651-L657
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L651-L657

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

theorem QEC.Coding.BDL26NativeSupportMetadata.event_labels_list (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ)
    (e : Event (P S n) J r) :
    [ (eventLabels S n J r e).1,(eventLabels S n J r e).2.1,
      (eventLabels S n J r e).2.2.1,(eventLabels S n J r e).2.2.2 ]=e.val.toList := by sorry
