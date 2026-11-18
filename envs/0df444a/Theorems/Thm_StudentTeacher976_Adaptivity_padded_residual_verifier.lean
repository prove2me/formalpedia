-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_padded_residual_verifier
-- name    : StudentTeacher976.Adaptivity.padded_residual_verifier
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:40:10.929195+00:00
-- url     : https://prove2.me/theorems/eef2e0fc-936c-498c-93b6-6eed3ee41344
-- title:
--   Polynomial-time parser and truncated residual verifier
-- statement:
--   Let $V$ be a finite deterministic oracle machine run with the empty oracle, with one polynomial clock that halts on every input. Fix a finite list of natural-coefficient polynomials $p_1,\ldots,p_\ell$.
--
--   There is another finite deterministic machine $M$, also run with the empty oracle, with one polynomial clock that halts on every string. On an encoded tuple whose first component is a word $s$ and whose remaining components are $z_1,\ldots,z_t$, it accepts exactly when $s$ is the canonical code of a pair $(x,y)$ and $V$ rejects the following tuple:
--
--   $$
--   \langle x,y,
--    z_1\mathbin{\upharpoonright}p_1(|x|),\ldots,
--    z_j\mathbin{\upharpoonright}p_j(|x|)\rangle,
--   \qquad j=\min(t,\ell).
--   $$
--
--   Here restriction means taking a prefix, so a word shorter than the requested prefix is retained in full. The two clocks are uniform over all strings, including empty and malformed inputs. In particular,
--
--   $$
--   M(\langle s,z_1,\ldots,z_t\rangle)=1
--   \quad\Longleftrightarrow\quad
--   \exists x,y:\ s=\langle x,y\rangle\ \land\
--   V(\langle x,y,z_1\upharpoonright p_1(|x|),\ldots,z_j\upharpoonright p_j(|x|)\rangle)=0.
--   $$
--
--   This is the pure polynomial-time parsing, truncation, and verifier-complement construction needed to pad the residual hierarchy quantifiers. It contains no hierarchy membership or game-solvability premise.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976 (October 2026), §1.2.1 pp.6–7, §3.1 p.19 (bounded existential hierarchy representation); standard exact-length padding implementation for the published tuple and finite-machine conventions; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Complexity
open QAdvFew.PoQOracle

namespace StudentTeacher976.Adaptivity

theorem padded_residual_verifier (V : OTM) (clock : Polynomial ℕ) (ps : List (Polynomial ℕ))
    (htotal : ∀ s : Word, (V.result (fun _ => false) s (clock.eval s.length)).isSome) :
    ∃ M : OTM, ∃ bound : Polynomial ℕ,
      (∀ s : Word, (M.result (fun _ => false) s (bound.eval s.length)).isSome) ∧
      ∀ (s : Word) (ys : List Word),
        M.result (fun _ => false) (tup (s :: ys)) (bound.eval (tup (s :: ys)).length) = some true ↔
          ∃ x y : Word, s = tup [x, y] ∧
            ¬ V.result (fun _ => false)
              (tup (x :: y :: List.zipWith (fun n w => w.take n) (ps.map fun p => p.eval x.length) ys))
              (clock.eval (tup (x :: y :: List.zipWith (fun n w => w.take n)
                (ps.map fun p => p.eval x.length) ys)).length) = some true := by sorry

end StudentTeacher976.Adaptivity
