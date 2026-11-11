-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keySupport_card_le
-- name    : QEC.Coding.BDL26KeyedGeometric.keySupport_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:57:48.216137+00:00
-- url     : https://prove2.me/theorems/1c0b5b09-34dc-4ecb-b5be-8563ceeb2d67
-- title:
--   BDL26 Keyed Geometric: key Support card le
-- statement:
--   The BDL26 Keyed Geometric construction uses the key Support card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L57-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L57-L64

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26KeyedGeometric.keySupport_card_le (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius : ℝ) (e : KeyEvent P key hk J radius) : (keySupport P key hk J radius e).card ≤ 12 := by sorry
