-- Prove2me | Theorems.Thm_ShiTM_copy_loop_transfers_stack
-- name    : ShiTM.copy_loop_transfers_stack
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T18:44:56.03444+00:00
-- url     : https://prove2.me/theorems/5a45c2e0-bb53-40d8-872b-0a66077ce607
-- title:
--   A pop-push loop transfers one stack onto another in one step per element
-- statement:
--   Suppose a multi-stack machine's program at some label is the loop that pops the source stack, tests whether the pop succeeded, and either pushes the popped symbol onto the target stack and returns to the same label, or jumps onward. Then starting from that label the machine reaches the onward label after exactly one step per source symbol plus one, with the source stack emptied and the target stack carrying the transferred symbols in reverse order on top of whatever it held before. Every other stack is untouched.
--
--   The count is one step per element because a single step executes an entire program tree, and the reversal is inherent to popping, so an order-preserving transfer is two instances of this lemma through a scratch stack. The state's role is abstracted into a load function, a success test and a read-back function together with the three laws relating them, so the lemma applies to any machine with this loop regardless of how its internal state is organised, and a translation between the two stack alphabets is carried explicitly since distinct stacks may have distinct alphabets.

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

theorem copy_loop_transfers_stack {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb} {e : Γ ka → Γ kb}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush (Turing.TM2.Stmt.goto (fun _ => lc)))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hcont : ∀ (w : σ) (y : Γ ka), gtest (fpop w (some y)) = true)
    (hstop : ∀ w : σ, gtest (fpop w none) = false)
    (hval : ∀ (w : σ) (y : Γ ka), hpush (fpop w (some y)) = e y)
    (s : List (Γ ka)) (v : σ) (S : ∀ k, List (Γ k)) (hS : S ka = s) :
    (fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step M))^[s.length + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (s.foldl (fun w y => fpop w (some y)) v) none,
               stk := Function.update (Function.update S ka []) kb
                        ((s.map e).reverse ++ S kb) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some lc, var := v, stk := S }
        (some { l := some lnext,
                var := fpop (s.foldl (fun w y => fpop w (some y)) v) none,
                stk := Function.update (Function.update S ka []) kb
                         ((s.map e).reverse ++ S kb) })
        (s.length + 1)) := by
  sorry

end ShiTM
