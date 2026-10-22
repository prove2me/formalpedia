-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_lemma_4_7
-- name    : TemperleyLieb.Gram.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:44.606072+00:00
-- url     : https://prove2.me/theorems/2696c649-cac7-4522-8b96-e33bd1f15be7
-- title:
--   Lemma 4.7, p. 19 — neighbouring seminormal norm ratio
-- statement:
--   Let $1\le k<n$ and let $s,t$ be tableaux of one shape with $t\triangleright s$. Write $e_k(s,t)$ for the coefficient of $f_s$ in $f_te_k$ in the seminormal basis. Suppose $e_k(s,t)\ne0$ and the shape at stage $k$ of $t$ is $(i,k-2i)$. Then
--
--   $$\langle f_s,f_s\rangle=\frac{p_{k-2i+1}(xp_{k-2i+2}-p_{k-2i+1})}{p_{k-2i+2}^2}\langle f_t,f_t\rangle=\frac{p_{k-2i+1}p_{k-2i+3}}{p_{k-2i+2}^2}\langle f_t,f_t\rangle.$$
--
--   Both displayed expressions are included. The ratio is the local norm change used in the branching law.
--
--   **Formalization Note** A basis with the displayed seminormal vectors is asserted to exist, and the coefficient is computed from its coordinate map; the theorem does not posit an unrelated coefficient function. The stage and generator indices are guarded.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 19, Lemma 4.7, using Eq. (4.2) on p. 17

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram
open QAlgorithms.Papers.Independent.Support21.P08

/-- Enyang, Lemma 4.7, p. 19: both displayed norm ratios for a nonzero
off-diagonal generator coefficient in the seminormal basis. -/
theorem lemma_4_7 (n : ℕ) (hn : 2 ≤ n) :
    ∃ D : FDatum n, IsMurphyDatum F xF n D ∧
      ∃ J : JMFamily D (n + 1), IsPaperJMFamily n D J ∧
        ∀ f : Fin (n / 2 + 1),
          (∃ B : Module.Basis (Tab n f) F (Tab n f → F),
            ∀ u, B u = seminormalVector J f u) ∧
          ∀ (B : Module.Basis (Tab n f) F (Tab n f → F)),
            (∀ u, B u = seminormalVector J f u) →
            ∀ (k : ℕ) (hk0 : 1 ≤ k) (hkn : k < n)
              (s t : Tab n f) (hst : s < t)
              (hcoeff : B.repr (cellAct D f (seminormalVector J f t)
                (e F xF n k)) s ≠ 0)
              (i : ℕ) (hi : cups t k = i),
              cellForm D f (seminormalVector J f s) (seminormalVector J f s) =
                ((algebraMap R F (p (k - 2 * i + 1)) *
                  (xF * algebraMap R F (p (k - 2 * i + 2)) -
                    algebraMap R F (p (k - 2 * i + 1)))) /
                  (algebraMap R F (p (k - 2 * i + 2))) ^ 2) *
                  cellForm D f (seminormalVector J f t) (seminormalVector J f t) ∧
              cellForm D f (seminormalVector J f s) (seminormalVector J f s) =
                ((algebraMap R F (p (k - 2 * i + 1)) *
                    algebraMap R F (p (k - 2 * i + 3))) /
                  (algebraMap R F (p (k - 2 * i + 2))) ^ 2) *
                  cellForm D f (seminormalVector J f t) (seminormalVector J f t) := by sorry

end TemperleyLieb.Gram
