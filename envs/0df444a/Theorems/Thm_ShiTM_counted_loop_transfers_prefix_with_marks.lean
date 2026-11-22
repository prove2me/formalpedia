-- Prove2me | Theorems.Thm_ShiTM_counted_loop_transfers_prefix_with_marks
-- name    : ShiTM.counted_loop_transfers_prefix_with_marks
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-16T07:26:04.677206+00:00
-- url     : https://prove2.me/theorems/5350183e-d663-4f5f-bb2b-ecc6a10c4470
-- title:
--   A generic three-stack loop that transcodes a prefix and counts it in unary
-- statement:
--   A general loop-induction principle for three-stack Turing machines, extending the two-stack transcoding loop with a counter. The loop pops symbols off a source stack and, for each symbol passing a test, pushes a transcoded symbol onto a second stack and a mark onto a third, halting on the first symbol that fails the test. For any machine whose loop label has this shape, the run on a stack consisting of a passing prefix, a failing symbol, and an arbitrary tail terminates in exactly one step per prefix symbol plus one, with the final configuration given exactly: the tail remains on the source stack, the transcoded prefix and the marks are prepended in reverse to the other two stacks, and the state is the left fold of the pop function over the prefix followed by the failing symbol. Both the exact iterate equation and the bounded-evaluation form are supplied, together with the length of the mark stack, which reads the count as a natural number, and a normal form expressing the marks as a replicated list when the mark function is constant. A counter must live on a stack rather than in the state because the state type is finite. Everything is arbitrary except the one loop label's statement.

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

open Turing Turing.TM2 Turing.TM2.Stmt

theorem counted_loop_transfers_prefix_with_marks {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Turing.TM2.Stmt Gam Lam sig) {ka kb kc : K}
    (hab : ka ≠ kb) (hac : ka ≠ kc) (hbc : kb ≠ kc) {lc lnext : Lam}
    {fpop : sig → Option (Gam ka) → sig} {gtest : sig → Bool}
    {hpush : sig → Gam kb} {hmark : sig → Gam kc}
    {e : Gam ka → Gam kb} {mk : Gam ka → Gam kc}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush
                (Turing.TM2.Stmt.push kc hmark (Turing.TM2.Stmt.goto (fun _ => lc))))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hval : forall (w : sig) (y : Gam ka), hpush (fpop w (some y)) = e y)
    (hmkv : forall (w : sig) (y : Gam ka), hmark (fpop w (some y)) = mk y)
    (p : List (Gam ka))
    (hcont : forall (w : sig) (y : Gam ka), y ∈ p → gtest (fpop w (some y)) = true)
    (c : Gam ka) (hstop : forall w : sig, gtest (fpop w (some c)) = false) (t : List (Gam ka))
    (v : sig) (S : forall k, List (Gam k)) (hS : S ka = p ++ c :: t) :
    (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) => cf.bind (Turing.TM2.step M))^[p.length + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
               stk := Function.update
                        (Function.update (Function.update S ka t) kb
                          ((List.map e p).reverse ++ S kb))
                        kc ((List.map mk p).reverse ++ S kc) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some lc, var := v, stk := S }
        (some { l := some lnext,
                var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
                stk := Function.update
                         (Function.update (Function.update S ka t) kb
                           ((List.map e p).reverse ++ S kb))
                         kc ((List.map mk p).reverse ++ S kc) })
        (p.length + 1))
    ∧ ((List.map mk p).reverse ++ S kc).length = p.length + (S kc).length
    ∧ (forall m : Gam kc, (forall y : Gam ka, mk y = m) →
          (List.map mk p).reverse ++ S kc = List.replicate p.length m ++ S kc) := by
  sorry

end ShiTM
