-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_neighbors
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_neighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:56:12.325137+00:00
-- url     : https://prove2.me/theorems/98584ce7-2be0-44cf-b02c-cfb637315772
-- title:
--   BDL26 Keyed Geometric: legacy neighbors
-- statement:
--   The BDL26 Keyed Geometric construction uses the legacy neighbors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L91-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L91-L109

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

theorem QEC.Coding.BDL26KeyedGeometric.legacy_neighbors (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    ((supportGraph (keySupport P (triangleKey P) (triangleKey_injective P) J r)).neighborFinset e).image
      (legacyEventEquiv P J r) =
      (supportGraph (eventSupport P J r)).neighborFinset (legacyEventEquiv P J r e) := by sorry
