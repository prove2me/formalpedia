-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_center
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:53:56.197393+00:00
-- url     : https://prove2.me/theorems/5d23b7bb-1457-4ac0-b83e-f858235c42cb
-- title:
--   BDL26 Keyed Geometric: legacy center
-- statement:
--   The BDL26 Keyed Geometric construction uses the legacy center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L38-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L38-L42

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

theorem QEC.Coding.BDL26KeyedGeometric.legacy_center (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r l : ℝ) (K : ℕ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r)
    (g : Grid K) :
    keyCenter P (triangleKey P) (triangleKey_injective P) J r l K e g =
      eventCenter P J r l K (legacyEventEquiv P J r e) g := by sorry
