-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_avoidance
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_avoidance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:57:32.613754+00:00
-- url     : https://prove2.me/theorems/41571590-e269-41c1-b3bc-88bed7e3d892
-- title:
--   BDL26 Keyed Geometric: legacy avoidance
-- statement:
--   The BDL26 Keyed Geometric construction uses the legacy avoidance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L111-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L111-L113

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

theorem QEC.Coding.BDL26KeyedGeometric.legacy_avoidance (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) :
    KeyAvoid P (triangleKey P) (triangleKey_injective P) J p = geometricAvoidance P J p := by sorry
