-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_supportGraph
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_supportGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:04:45.339186+00:00
-- url     : https://prove2.me/theorems/bb348d3c-062c-4c99-b0db-9d0239d1205d
-- title:
--   BDL26 Keyed Geometric: legacy support Graph
-- statement:
--   The BDL26 Keyed Geometric construction uses the legacy support Graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L85-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L85-L89

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

theorem QEC.Coding.BDL26KeyedGeometric.legacy_supportGraph (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    (supportGraph (keySupport P (triangleKey P) (triangleKey_injective P) J r)).Adj e f ↔
      (supportGraph (eventSupport P J r)).Adj
        (legacyEventEquiv P J r e) (legacyEventEquiv P J r f) := by sorry
