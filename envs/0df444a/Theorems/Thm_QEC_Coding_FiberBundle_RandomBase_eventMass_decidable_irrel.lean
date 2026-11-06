-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_decidable_irrel
-- name    : QEC.Coding.FiberBundle.RandomBase.eventMass_decidable_irrel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:28:35.139526+00:00
-- url     : https://prove2.me/theorems/a6a728ea-68ca-4b25-bb99-94b5fb88741f
-- title:
--   Random Base: event Mass decidable irrel
-- statement:
--   The finite event mass is independent of the chosen decision procedure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L192-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L192-L199

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u

theorem QEC.Coding.FiberBundle.RandomBase.eventMass_decidable_irrel
    {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop)
    (d₁ d₂ : DecidablePred event) :
    @eventMass Ω inferInstance p event d₁ =
      @eventMass Ω inferInstance p event d₂ := by sorry
