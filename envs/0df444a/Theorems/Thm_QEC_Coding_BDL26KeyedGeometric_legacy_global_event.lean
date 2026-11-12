-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_global_event
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_global_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:04:30.807272+00:00
-- url     : https://prove2.me/theorems/36fd8e54-38c9-4b2b-bd9f-ece4ea5be70c
-- title:
--   BDL26 Keyed Geometric: legacy global event
-- statement:
--   The BDL26 Keyed Geometric construction uses the legacy global event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L77-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L77-L83

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

theorem QEC.Coding.BDL26KeyedGeometric.legacy_global_event (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r l : ℝ) (K : ℕ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    localEvent (X := fun _ : Vertex P => Space)
      (keySupport P (triangleKey P) (triangleKey_injective P) J r)
      (keyBad P (triangleKey P) (triangleKey_injective P) J r l K) e =
      localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P J r) (eventBad P J r l K) (legacyEventEquiv P J r e) := by sorry
