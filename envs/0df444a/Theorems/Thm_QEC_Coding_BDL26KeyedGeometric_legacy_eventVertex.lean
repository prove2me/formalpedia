-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_eventVertex
-- name    : QEC.Coding.BDL26KeyedGeometric.legacy_eventVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:53:05.933714+00:00
-- url     : https://prove2.me/theorems/ca02332a-38d7-43fb-bff5-84ab80d2c89d
-- title:
--   BDL26 Keyed Geometric: legacy event Vertex
-- statement:
--   The BDL26 Keyed Geometric construction uses the legacy event Vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L54-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean#L54-L58

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

theorem QEC.Coding.BDL26KeyedGeometric.legacy_eventVertex (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r)
    (a : e.val) (i : Fin 3) :
    legacySupportEquiv P J r e (keyVertex P (triangleKey P) (triangleKey_injective P) J r e a i) =
      eventVertex P J r (legacyEventEquiv P J r e) ⟨a.val,a.property⟩ i := by sorry
