-- Prove2me | Theorems.Thm_ShiTM_branch_loop_transfers_prefix_until_symbol
-- name    : ShiTM.branch_loop_transfers_prefix_until_symbol
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-16T07:05:59.675475+00:00
-- url     : https://prove2.me/theorems/2a8a9d85-eda1-4d90-8f57-ec588cc52e3f
-- title:
--   A generic two-stack loop that transcodes a prefix and halts on a distinguished symbol
-- statement:
--   A general loop-induction principle for two-stack Turing machines: a loop that pops symbols off one stack, transcodes each onto a second stack, and halts on the first symbol failing a test. For any machine whose loop label pops, branches on the updated state, and either pushes and loops or jumps to an exit label, the run on a stack consisting of a passing prefix, then a failing symbol, then an arbitrary tail terminates in exactly one step per prefix symbol plus one. The final configuration is given exactly: the tail remains on the source stack, the transcoded prefix is prepended in reverse to the target stack, and the state is the left fold of the pop function over the prefix followed by the failing symbol. Both the exact iterate equation and the bounded-evaluation form are supplied. Note the pop happens before the branch, so the failing symbol is consumed on both arms and its state update is applied. Everything is arbitrary except the one loop label's statement: the stack index type, the alphabet family, the label and state types, the two stack keys, and all four functions.

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

open Turing Turing.TM2 Turing.TM2.Stmt

theorem branch_loop_transfers_prefix_until_symbol {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb} {e : Γ ka → Γ kb}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush (Turing.TM2.Stmt.goto (fun _ => lc)))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hval : ∀ (w : σ) (y : Γ ka), hpush (fpop w (some y)) = e y)
    (p : List (Γ ka)) (hcont : ∀ (w : σ) (y : Γ ka), y ∈ p → gtest (fpop w (some y)) = true)
    (c : Γ ka) (hstop : ∀ w : σ, gtest (fpop w (some c)) = false) (t : List (Γ ka))
    (v : σ) (S : ∀ k, List (Γ k)) (hS : S ka = p ++ c :: t) :
    (fun cf : Option (Turing.TM2.Cfg Γ Λ σ) => cf.bind (Turing.TM2.step M))^[p.length + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
               stk := Function.update (Function.update S ka t) kb
                        ((List.map e p).reverse ++ S kb) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some lc, var := v, stk := S }
        (some { l := some lnext,
                var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
                stk := Function.update (Function.update S ka t) kb
                         ((List.map e p).reverse ++ S kb) })
        (p.length + 1)) := by
  sorry

end ShiTM
