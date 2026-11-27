-- Prove2me | Theorems.Thm_PvsNP_StockSingleTapeTime_polytime_stock_TM1
-- name    : PvsNP.StockSingleTapeTime.polytime_stock_TM1
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T02:44:34.795082+00:00
-- url     : https://prove2.me/theorems/b29a0c60-9829-46ac-ab8f-cbae29ea7225
-- title:
--   The stock single-tape translation preserves polynomial time
-- statement:
--   Given a bundled polynomial-time Mathlib TM2 algorithm, there is a polynomial in the encoded input length that bounds its translated TM1 run. This one-tape run reaches a halting configuration that represents the exact stock output stacks.
-- source:
--   Counted simulation for the Mathlib TM2to1 translation. The classical single-tape simulation bound goes back to Hartmanis and Stearns (1965), doi:10.1090/S0002-9947-1965-0170805-7.

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2to1

theorem PvsNP.StockSingleTapeTime.polytime_stock_TM1 {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (alg : TM2ComputableInPolyTime ea eb f) :
    let tm := alg.tm
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ p : Polynomial ℕ, ∀ a, ∃ target',
      TrCfg (haltList tm ((eb (f a)).map alg.outputAlphabet.invFun)) target' ∧
      TM1.step (tr tm.m) target' = none ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr tm.m))
        (TM1.init (trInit tm.k₀ ((ea a).map alg.inputAlphabet.invFun))) (some target')
        (p.eval (ea a).length)) := by sorry
