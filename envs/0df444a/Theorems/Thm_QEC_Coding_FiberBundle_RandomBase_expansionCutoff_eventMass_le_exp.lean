-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_expansionCutoff_eventMass_le_exp
-- name    : QEC.Coding.FiberBundle.RandomBase.expansionCutoff_eventMass_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:24.009488+00:00
-- url     : https://prove2.me/theorems/8b5d8dec-193e-40ac-8542-e96d6944a0b6
-- title:
--   Random Base: expansion Cutoff event Mass le exp
-- statement:
--   Uniform exponential lower-tail bound at the strengthened HHO20 expansion
--   cutoff.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1075-L1106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1075-L1106

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.expansionCutoff_eventMass_le_exp
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample =>
          (checkSetNeighborhood sample S).card ≤
            expansionCutoff Delta S) ≤
      ENNReal.ofReal
        (Real.exp (-((Delta : Real) * S.card / 1000))) := by sorry
