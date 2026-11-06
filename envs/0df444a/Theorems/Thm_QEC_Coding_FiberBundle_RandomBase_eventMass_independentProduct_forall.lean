-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_independentProduct_forall
-- name    : QEC.Coding.FiberBundle.RandomBase.eventMass_independentProduct_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:28:16.01933+00:00
-- url     : https://prove2.me/theorems/4cc9282d-31cb-4d6d-b2d0-a7fb59b258e5
-- title:
--   Random Base: event Mass independent Product forall
-- statement:
--   An all-coordinate event under `independentProduct` factors into the product
--   of its coordinate event masses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L134-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean#L134-L165

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

theorem QEC.Coding.FiberBundle.RandomBase.eventMass_independentProduct_forall
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type u} [∀ i, Fintype (κ i)]
    (p : ∀ i, PMF (κ i))
    (event : ∀ i, κ i → Prop)
    [∀ i, DecidablePred (event i)] :
    eventMass
        (independentProduct p)
        (fun x => ∀ i, event i (x i)) =
      ∏ i, eventMass (p i) (event i) := by sorry
