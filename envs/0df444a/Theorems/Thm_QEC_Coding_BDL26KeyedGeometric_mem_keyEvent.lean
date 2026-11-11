-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_mem_keyEvent
-- name    : QEC.Coding.BDL26KeyedGeometric.mem_keyEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:42:56.883267+00:00
-- url     : https://prove2.me/theorems/c65d8367-bb0d-4b58-9ac0-2be89c287e0e
-- title:
--   BDL26 Keyed Geometric: mem key Event
-- statement:
--   The actual global event is exactly the pullback of its local support predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L115-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L115-L123

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

theorem QEC.Coding.BDL26KeyedGeometric.mem_keyEvent (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : KeyEvent P key hk J radius) (p : Vertex P → Space) :
    p ∈ localEvent (keySupport P key hk J radius) (keyBad P key hk J radius lambda K) e ↔
      ∃ g : Grid K, ∀ a : e.val,
        (fun i => p (triangleVertex P a.val i)) ∈
          triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
            (keyCenter P key hk J radius lambda K e g) 2 := by sorry
