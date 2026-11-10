-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mem_global_event
-- name    : QEC.Coding.BDL26RandomPerturbation.mem_global_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:00:33.245864+00:00
-- url     : https://prove2.me/theorems/8f8e7fc8-28db-4228-b9af-62467a8f2f0a
-- title:
--   BDL26 Random Perturbation: mem global event
-- statement:
--   The actual global event is exactly the pullback of its local support predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean#L108-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean#L108-L115

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.mem_global_event (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) (p : Vertex P → Space) :
    p ∈ localEvent (eventSupport P J radius) (eventBad P J radius lambda K) e ↔
      ∃ g : Grid K, ∀ a : e.val,
        (fun i => p (triangleVertex P a.val i)) ∈
          triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
            (eventCenter P J radius lambda K e g) 2 := by sorry
