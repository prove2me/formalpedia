-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyAnchor_key_le
-- name    : QEC.Coding.BDL26KeyedGeometric.keyAnchor_key_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:57:53.441423+00:00
-- url     : https://prove2.me/theorems/3ed78015-29e1-4e75-8815-f250635af445
-- title:
--   BDL26 Keyed Geometric: key Anchor key le
-- statement:
--   The chosen anchor minimizes the actual key on every original label in the event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L139-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L139-L144

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

theorem QEC.Coding.BDL26KeyedGeometric.keyAnchor_key_le (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) (a : Triangle P) (ha : a ∈ e.val) :
    key (keyAnchor P key hk J radius e) ≤ key a := by sorry
