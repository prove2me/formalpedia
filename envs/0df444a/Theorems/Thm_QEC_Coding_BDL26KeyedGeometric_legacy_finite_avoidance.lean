-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_finite_avoidance
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_finite_avoidance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:59:34.670792+00:00
-- url     : https://prove2.me/theorems/1baccc47-947b-4090-b67c-370ea2df7d8b
-- title:
--   BDL26 Keyed Geometric: legacy finite avoidance
-- statement:
--   Arbitrary finite event selections, not only the full-universe avoidance set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L116-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L116-L134

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

theorem QEC.Coding.BDL26KeyedGeometric.legacy_finite_avoidance (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r l : ℝ) (K : ℕ)
    (s : Finset (KeyEvent P (triangleKey P) (triangleKey_injective P) J r)) :
    avoid (localEvent (X := fun _ : Vertex P => Space)
      (keySupport P (triangleKey P) (triangleKey_injective P) J r)
      (keyBad P (triangleKey P) (triangleKey_injective P) J r l K)) s =
      avoid (localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P J r) (eventBad P J r l K))
        (s.image (legacyEventEquiv P J r)) := by sorry
