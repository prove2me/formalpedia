-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyAnchor_unique
-- name    : QEC.Coding.BDL26KeyedGeometric.keyAnchor_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:58:04.460239+00:00
-- url     : https://prove2.me/theorems/4b0e49b4-c452-4939-958f-0125ae99b634
-- title:
--   BDL26 Keyed Geometric: key Anchor unique
-- statement:
--   The BDL26 Keyed Geometric construction uses the key Anchor unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L146-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L146-L152

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

theorem QEC.Coding.BDL26KeyedGeometric.keyAnchor_unique (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) (a : Triangle P) (ha : a ∈ e.val)
    (hmin : ∀ b ∈ e.val, key a ≤ key b) : keyAnchor P key hk J radius e = a := by sorry
