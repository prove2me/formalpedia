-- Prove2me | Theorems.Thm_ShiTM_unary_count_to_dispatch_symbol
-- name    : ShiTM.unary_count_to_dispatch_symbol
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-16T10:41:18.226859+00:00
-- url     : https://prove2.me/theorems/5ad941ff-43f1-4155-8929-4cc7a4c9d7c1
-- title:
--   Converting a parsed unary count into a dispatchable symbol
-- statement:
--   A stack machine converts a parsed unary count into a single symbol that a dispatcher can branch on. A prefix parser leaves a value as a run of identical marks, but selecting one of finitely many code paths requires a symbol whose identity determines the path, and nothing connects the two representations. The block here consumes the marks along a chain of labels, so that the count is carried by the label index rather than by the machine's state, and when the marks run out it pushes the symbol assigned to that index. The run costs one step per mark plus one, the mark stack is left holding the remainder, and the pushed symbol is the head of the target stack, which is exactly what a dispatcher reads. The statement is bounded: since the state type, the stack alphabets and the program are all finite, no machine can emit a symbol for an arbitrarily large count, so the count is assumed below a fixed bound and the symbol family is supplied by the caller. Carrying the counter in the state instead would require an increment law that is unsatisfiable for a finite state type. The run is terminated either by a distinguished symbol or by the bottom of the stack, the latter being what a prefix parser leaves on an initially empty stack.

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

open Turing Turing.TM2 Turing.TM2.Stmt

theorem unary_count_to_dispatch_symbol {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Turing.TM2.Stmt Gam Lam sig) {kmark ktag : K} (hab : kmark ≠ ktag)
    {fpop : sig → Option (Gam kmark) → sig} {gmark : sig → Bool}
    (B : ℕ) (lab : ℕ → Lam) (lnext : Lam) (tagOf : ℕ → Gam ktag)
    (hM : ∀ i, i < B → M (lab i) = Turing.TM2.Stmt.pop kmark fpop
            (Turing.TM2.Stmt.branch gmark
              (Turing.TM2.Stmt.goto (fun _ => lab (i + 1)))
              (Turing.TM2.Stmt.push ktag (fun _ => tagOf i)
                (Turing.TM2.Stmt.goto (fun _ => lnext)))))
    (mark : Gam kmark) (hmark : ∀ w : sig, gmark (fpop w (some mark)) = true)
    (tl : List (Gam kmark)) (hstop : ∀ w : sig, gmark (fpop w tl.head?) = false)
    (c : ℕ) (hc : c < B) (v : sig) (S : ∀ k, List (Gam k))
    (hS : S kmark = List.replicate c mark ++ tl) :
    (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) => cf.bind (Turing.TM2.step M))^[c + 1]
        (some { l := some (lab 0), var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v
                        (List.replicate c mark)) tl.head?,
               stk := Function.update (Function.update S kmark tl.tail) ktag
                        (tagOf c :: S ktag) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some (lab 0), var := v, stk := S }
        (some { l := some lnext,
                var := fpop (List.foldl (fun w y => fpop w (some y)) v
                         (List.replicate c mark)) tl.head?,
                stk := Function.update (Function.update S kmark tl.tail) ktag
                         (tagOf c :: S ktag) })
        (c + 1))
    ∧ (Function.update (Function.update S kmark tl.tail) ktag (tagOf c :: S ktag)) kmark
        = tl.tail
    ∧ (Function.update (Function.update S kmark tl.tail) ktag (tagOf c :: S ktag)) ktag
        = tagOf c :: S ktag
    ∧ ((Function.update (Function.update S kmark tl.tail) ktag
        (tagOf c :: S ktag)) ktag).head? = some (tagOf c) := by
  sorry

end ShiTM
