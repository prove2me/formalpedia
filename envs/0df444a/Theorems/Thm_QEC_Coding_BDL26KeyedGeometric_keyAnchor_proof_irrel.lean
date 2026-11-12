-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyAnchor_proof_irrel
-- name    : QEC.Coding.BDL26KeyedGeometric.keyAnchor_proof_irrel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:42:49.061923+00:00
-- url     : https://prove2.me/theorems/22d2a07a-fea8-437b-ba38-66b490e46e86
-- title:
--   BDL26 Keyed Geometric: key Anchor proof irrel
-- statement:
--   Injectivity witnesses are proofs, not an additional anchor policy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L155-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L155-L158

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

theorem QEC.Coding.BDL26KeyedGeometric.keyAnchor_proof_irrel (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk hk' : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) :
    keyAnchor P key hk J radius e = keyAnchor P key hk' J radius e := by sorry
