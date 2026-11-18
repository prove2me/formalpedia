-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_padded_residual_program
-- name    : StudentTeacher976.Adaptivity.padded_residual_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:39:28.074632+00:00
-- url     : https://prove2.me/theorems/14f38904-458c-4ce1-91af-6507e9945879
-- title:
--   A finite-control program parses and trims residual certificates
-- statement:
--   Fix a finite verifier $V$ with an empty oracle and one polynomial clock valid on every string. Let $p_1,\ldots,p_\ell$ be fixed certificate-length polynomials. There is a finite-control two-tape program $P$ with one polynomial halting clock on every input, such that on a tuple whose first component is $s$ and whose remaining components are $w_1,\ldots,w_a$, it accepts exactly when
--
--   $$
--   \exists x,y:\ s=\langle x,y\rangle\quad\text{and}\quad
--   V(\langle x,y,w_1{\upharpoonright}p_1(|x|),\ldots,w_d{\upharpoonright}p_d(|x|)\rangle)\ne1,
--   \qquad d=\min(a,\ell).
--   $$
--
--   Here $w\upharpoonright n$ denotes the prefix of at most $n$ bits. Malformed first components reject; surplus components are ignored. All machines, finite sets and polynomials are fixed before the input. This is the operational program needed by exact-length alternating-quantifier padding.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, §1.2.1 pp.6–7 and §3.1 p.19. Operational simulation and exact-quantifier padding bridges for the published machine definitions. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_FiniteControl

namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle
open QAdvFew.PoQOracle.OTM.FiniteControl

theorem padded_residual_program (V : OTM) (clock : Polynomial ℕ) (ps : List (Polynomial ℕ))
    (htotal : ∀ s : Word, (V.result (fun _ => false) s (clock.eval s.length)).isSome) :
    ∃ (Q A : Type) (_ : Fintype Q) (_ : Fintype A), ∃ P : Program Q A, ∃ bound : Polynomial ℕ,
      (∀ s : Word, ∃ b : Bool,
        ((P.step (fun _ => false))^[bound.eval s.length] (P.initial s)).state = Sum.inl b) ∧
      ∀ (s : Word) (ys : List Word),
        ((P.step (fun _ => false))^[bound.eval (tup (s :: ys)).length]
          (P.initial (tup (s :: ys)))).state = Sum.inl true ↔
          ∃ x y : Word, s = tup [x, y] ∧
            ¬ V.result (fun _ => false)
              (tup (x :: y :: List.zipWith (fun n w => w.take n) (ps.map fun p => p.eval x.length) ys))
              (clock.eval (tup (x :: y :: List.zipWith (fun n w => w.take n)
                (ps.map fun p => p.eval x.length) ys)).length) = some true := by sorry

end StudentTeacher976.Adaptivity
