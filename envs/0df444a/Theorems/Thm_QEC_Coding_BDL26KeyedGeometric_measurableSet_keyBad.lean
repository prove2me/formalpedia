-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_measurableSet_keyBad
-- name    : QEC.Coding.BDL26KeyedGeometric.measurableSet_keyBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:32:56.654339+00:00
-- url     : https://prove2.me/theorems/b9cc17c9-f4fc-4f79-ac02-0895bd01b751
-- title:
--   BDL26 Keyed Geometric: measurable Set key Bad
-- statement:
--   The BDL26 Keyed Geometric construction uses the measurable Set key Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L104-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L104-L112

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

theorem QEC.Coding.BDL26KeyedGeometric.measurableSet_keyBad (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius) :
    MeasurableSet (keyBad P key hk J radius lambda K e) := by sorry
