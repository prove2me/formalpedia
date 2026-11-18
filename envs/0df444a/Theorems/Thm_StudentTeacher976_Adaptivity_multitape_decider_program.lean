-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_multitape_decider_program
-- name    : StudentTeacher976.Adaptivity.multitape_decider_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:33:14.552198+00:00
-- url     : https://prove2.me/theorems/6e394347-e486-414e-b594-4e537e3d32f0
-- title:
--   Multiple-tape Boolean deciders have finite two-tape programs
-- statement:
--   Let $M$ be a deterministic binary multiple-tape machine with finitely many states and a polynomial halting clock $p$ on every input. There is a fixed finite-control two-tape program $P$ and a polynomial clock $q$ such that, on every input $x$,
--
--   $$
--   P(x)\text{ halts with the first output bit of }M(x),
--   $$
--
--   using false if that output is empty. Its finite states and alphabet are fixed before $x$. The statement uses actual runs of both machine models and makes no oracle or hierarchy-closure assumption. This bridge allows the multiple-tape list-computation calculus to supply operational padding verifiers.
-- source:
--   Implementation bridges for Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, §1.2.1 pp.6–7 and §3.1 p.19; the published finite oracle-machine and Cslib deterministic multiple-tape interfaces. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_FiniteControl
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic

theorem StudentTeacher976.Adaptivity.multitape_decider_program
    {k : ℕ} {S : Type} [Fintype S] (M : Turing.MultiTapeTM k Bool S)
    (clock : Polynomial ℕ)
    (htotal : ∀ x : List Bool, (M.runFrom (M.initCfg x) (clock.eval x.length)).Halted) :
    ∃ (Q A : Type) (_ : Fintype Q) (_ : Fintype A),
      ∃ P : QAdvFew.PoQOracle.OTM.FiniteControl.Program Q A, ∃ bound : Polynomial ℕ,
      ∀ x : List Bool,
        ((P.step (fun _ => false))^[bound.eval x.length] (P.initial x)).state =
          Sum.inl ((M.runFrom (M.initCfg x) (clock.eval x.length)).output.head?.getD false) := by sorry
