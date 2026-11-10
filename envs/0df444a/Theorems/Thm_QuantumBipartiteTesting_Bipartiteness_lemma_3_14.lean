-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_14
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:13:01.529201+00:00
-- url     : https://prove2.me/theorems/c758f2b7-fca7-47bb-ac7f-059df2c36493
-- title:
--   Lemma 3.14 — reciprocal of bounded affine factors
-- statement:
--   Let $z_1,\dots,z_d$ be arbitrary real affine bivariate polynomials, let $C>0$, and let $\mathcal R$ be any real region on which every $|z_i|\le1/4$. Set $D=C\prod_i(1-z_i)$. Then there is one real polynomial $A$ satisfying
--   $$\deg A\le4d+10,\qquad |D(M,\ell)A(M,\ell)-1|\le10^{-2}$$
--   throughout $\mathcal R$. The region need not be an integer grid, bounded, closed or nonempty. The number $d$ counts factors and is unrelated to graph degree. This gives the uniform reciprocal estimate used by the explicit construction.
--
--   Differences from the source:
--   - encoding: a given polynomial D_q=C product_i(1-z_i) → the product polynomial is written directly inside the conclusion; reason: substituting the source equality recovers exactly its statement, without an unrelated free denominator
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 3.14, PDF = printed page 18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_3_14 (d : ℕ) (z : Fin d → Bivariate)
    (haffine : ∀ i, (z i).totalDegree ≤ 1) (C : ℝ) (hC : 0 < C) (region : Set (ℝ × ℝ))
    (hz : ∀ x ∈ region, ∀ i, |Eval (z i) x.1 x.2| ≤ 1/4) :
    ∃ A : Bivariate, A.totalDegree ≤ 4*d+10 ∧
      ∀ x ∈ region, |Eval (MvPolynomial.C C * ∏ i, (1-z i)) x.1 x.2 * Eval A x.1 x.2 - 1| ≤ 1/100 := by sorry

end QuantumBipartiteTesting.Bipartiteness
