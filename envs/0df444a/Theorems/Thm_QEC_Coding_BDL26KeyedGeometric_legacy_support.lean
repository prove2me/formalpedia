-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_support
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:51:02.525417+00:00
-- url     : https://prove2.me/theorems/956b815a-fad7-4a56-9dfe-351e78b268b0
-- title:
--   BDL26 Keyed Geometric: legacy support
-- statement:
--   The BDL26 Keyed Geometric construction uses the legacy support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L28-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L28-L31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleKey_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26KeyedGeometric.legacy_support (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    keySupport P (triangleKey P) (triangleKey_injective P) J r e =
      eventSupport P J r (legacyEventEquiv P J r e) := by sorry
