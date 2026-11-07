-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_failureMass_decidable_irrel
-- name    : QEC.Coding.FiberBundle.RandomBase.failureMass_decidable_irrel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:45:03.474206+00:00
-- url     : https://prove2.me/theorems/3c394ff0-37b7-443e-957f-694e8aa447e1
-- title:
--   Random Base: failure Mass decidable irrel
-- statement:
--   The finite failure mass is independent of the chosen decision procedure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L956-L963
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L956-L963

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.failureMass_decidable_irrel
    {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (event : Ω → Prop)
    (d₁ d₂ : DecidablePred event) :
    @failureMass Ω inferInstance p event d₁ =
      @failureMass Ω inferInstance p event d₂ := by sorry
