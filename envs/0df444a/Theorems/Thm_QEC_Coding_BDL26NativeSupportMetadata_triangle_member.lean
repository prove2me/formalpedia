-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_triangle_member
-- name    : QEC.Coding.BDL26NativeSupportMetadata.triangle_member
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:56:07.322202+00:00
-- url     : https://prove2.me/theorems/8caa02fd-6fba-4840-8cc4-2956d11aedfc
-- title:
--   BDL26 Native Support Metadata: triangle member
-- statement:
--   The BDL26 Native Support Metadata construction uses the triangle member property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L556-L558
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L556-L558

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

theorem QEC.Coding.BDL26NativeSupportMetadata.triangle_member (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    triangleCode S n t∈T S n := by sorry
