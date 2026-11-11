-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyEvent_card_le
-- name    : QEC.Coding.BDL26KeyedGeometric.keyEvent_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:56:46.504351+00:00
-- url     : https://prove2.me/theorems/25e097cb-a8b2-4e9e-bbd2-2dd5734e3aac
-- title:
--   BDL26 Keyed Geometric: key Event card le
-- statement:
--   The BDL26 Keyed Geometric construction uses the key Event card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L74-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L74-L87

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

theorem QEC.Coding.BDL26KeyedGeometric.keyEvent_card_le (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ) :
    Fintype.card (KeyEvent P key hk J radius) ≤ Fintype.card (Triangle P)^4 := by sorry
