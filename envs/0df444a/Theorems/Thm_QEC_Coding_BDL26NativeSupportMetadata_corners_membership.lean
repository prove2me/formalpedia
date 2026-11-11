-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_corners_membership
-- name    : QEC.Coding.BDL26NativeSupportMetadata.corners_membership
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:53:55.740018+00:00
-- url     : https://prove2.me/theorems/c1cffb51-3589-47c7-b6cc-12286b9eb141
-- title:
--   BDL26 Native Support Metadata: corners membership
-- statement:
--   The BDL26 Native Support Metadata construction uses the corners membership property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L618-L640
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L618-L640

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

theorem QEC.Coding.BDL26NativeSupportMetadata.corners_membership (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (a : Index S n) :
    a∈tripleList (corners S n t) ↔
      BDL26NativeStateRows.decode S n a∈triangleSupport (P S n) t := by sorry
