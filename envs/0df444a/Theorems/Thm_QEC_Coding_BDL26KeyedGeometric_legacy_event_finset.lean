-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_event_finset
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_event_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:50:23.46527+00:00
-- url     : https://prove2.me/theorems/e44d10ee-bec1-4796-8c8c-4d78021c971b
-- title:
--   BDL26 Keyed Geometric: legacy event finset
-- statement:
--   The BDL26 Keyed Geometric construction uses the legacy event finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L24-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L24-L26

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

theorem QEC.Coding.BDL26KeyedGeometric.legacy_event_finset (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    (legacyEventEquiv P J r e).val = e.val := by sorry
