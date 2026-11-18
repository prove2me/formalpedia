-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_padded_residual_multitape
-- name    : StudentTeacher976.Adaptivity.padded_residual_multitape
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:32:47.002428+00:00
-- url     : https://prove2.me/theorems/10c0cdc8-8f38-486e-8365-dd88ab70b5c7
-- title:
--   A binary multiple-tape verifier parses and trims residual certificates
-- statement:
--   Let $V$ be a fixed empty-oracle verifier with one polynomial halting clock on all strings, and fix certificate-length polynomials $p_1,\ldots,p_\ell$. There is a finite binary multiple-tape machine $M$ with one polynomial clock on all strings, whose first output bit is true on an input tuple with first component $s$ and remaining components $w_1,\ldots,w_a$ exactly when
--
--   $$
--   \exists x,y:\ s=\langle x,y\rangle\quad\text{and}\quad
--   V(\langle x,y,w_1{\upharpoonright}p_1(|x|),\ldots,w_d{\upharpoonright}p_d(|x|)\rangle)\ne1,
--   \qquad d=\min(a,\ell).
--   $$
--
--   The notation $w\upharpoonright n$ denotes a prefix of at most $n$ bits. Malformed first components reject and surplus components are ignored. This is the concrete list-processing implementation required by residual quantifier padding; the separate machine-model compiler transfers it to the mission's two-tape programs.
-- source:
--   Implementation bridges for Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, §1.2.1 pp.6–7 and §3.1 p.19; the published finite oracle-machine and Cslib deterministic multiple-tape interfaces. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_FiniteControl
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic

namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle

theorem padded_residual_multitape (V : OTM) (clock : Polynomial ℕ) (ps : List (Polynomial ℕ))
    (htotal : ∀ s : Word, (V.result (fun _ => false) s (clock.eval s.length)).isSome) :
    ∃ (k : ℕ) (S : Type) (_ : Fintype S), ∃ M : Turing.MultiTapeTM k Bool S, ∃ bound : Polynomial ℕ,
      (∀ s : Word, (M.runFrom (M.initCfg s) (bound.eval s.length)).Halted) ∧
      ∀ (s : Word) (ys : List Word),
        (M.runFrom (M.initCfg (tup (s :: ys))) (bound.eval (tup (s :: ys)).length)).output.head?.getD false = true ↔
          ∃ x y : Word, s = tup [x, y] ∧
            ¬ V.result (fun _ => false)
              (tup (x :: y :: List.zipWith (fun n w => w.take n) (ps.map fun p => p.eval x.length) ys))
              (clock.eval (tup (x :: y :: List.zipWith (fun n w => w.take n)
                (ps.map fun p => p.eval x.length) ys)).length) = some true := by sorry

end StudentTeacher976.Adaptivity
