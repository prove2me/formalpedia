-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_regular_representation_idempotent_resolution
-- name    : WeierstrassEllipticZeta.regular_representation_idempotent_resolution
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T17:52:54.540436+00:00
-- url     : https://prove2.me/theorems/9a072688-7470-4b97-a37a-aa49ea52d237
-- title:
--   Quotient-ring idempotents realizing a commuting projector resolution
-- statement:
--   Let $R$ be a commutative ring and $B$ a commutative $R$-algebra with a finite basis $\beta$ indexed by a finite type $N$. Let
--   $$
--   b:B\xrightarrow{\;\sim\;}R^N
--   $$
--   be the coordinate equivalence associated with $\beta$, and let $L_a$ denote multiplication by $a\in B$ in these coordinates. Suppose that a finite family of $R$-linear endomorphisms $P_i$ of $R^N$ satisfies
--   $$
--   P_iL_a=L_aP_i\quad(a\in B),\qquad
--   P_i^2=P_i,\qquad P_iP_j=0\quad(i\ne j),\qquad
--   \sum_iP_i=\operatorname{id}.
--   $$
--   Then there are elements $\varepsilon_i\in B$ with
--   $$
--   L_{\varepsilon_i}=P_i,\qquad
--   \varepsilon_i=b^{-1}(P_i(b(1))),\qquad
--   \varepsilon_i^2=\varepsilon_i,\qquad
--   \varepsilon_i\varepsilon_j=0\quad(i\ne j),\qquad
--   \sum_i\varepsilon_i=1.
--   $$
--   Thus the projector resolution is realized by a family of pairwise annihilating algebra idempotents. A field, nontrivial algebra or nonempty index type is not assumed.
-- source:
--   Derived commutative-algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. For a commutative algebra with a finite basis, a projector resolution commuting with every regular multiplication operator is realized by multiplication by explicit algebra elements. Each element is obtained by applying its projector to the coordinates of 1 and decoding with the basis. Faithfulness transfers idempotence, pairwise annihilation and sum-to-identity to these elements. Works over a commutative base ring; no nontriviality or nonempty-index assumption. Mathlib-only proof with no new definitions or Prove2Me theorem dependencies.

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Ring.Idempotent

open scoped Classical

theorem WeierstrassEllipticZeta.regular_representation_idempotent_resolution
    (R B n ι : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [Fintype n] [DecidableEq n] [Fintype ι]
    (β : Module.Basis n R B) (P : ι → Module.End R (n → R))
    (hcomm : ∀ (a : B) (i : ι),
      Commute (P i) (Algebra.leftMulMatrix β a).mulVecLin)
    (hidem : ∀ i, IsIdempotentElem (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (hsum : (∑ i, P i) = 1) :
    ∃ ε : ι → B,
      (∀ i, (Algebra.leftMulMatrix β (ε i)).mulVecLin = P i) ∧
      (∀ i, ε i = β.equivFun.symm (P i (β.equivFun 1))) ∧
      (∀ i, IsIdempotentElem (ε i)) ∧
      (∀ i j, i ≠ j → ε i * ε j = 0) ∧
      (∑ i, ε i) = 1 := by sorry
