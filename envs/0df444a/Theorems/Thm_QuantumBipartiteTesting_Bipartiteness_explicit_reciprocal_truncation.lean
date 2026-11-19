-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_explicit_reciprocal_truncation
-- name    : QuantumBipartiteTesting.Bipartiteness.explicit_reciprocal_truncation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:25:13.538123+00:00
-- url     : https://prove2.me/theorems/21d5ffe3-d782-4cad-8cdb-17a6dceb4bd1
-- title:
--   Explicit total-degree geometric reciprocal truncation
-- statement:
--   Let $I$ be a finite index set of cardinality $d$, let $z_i(M,\ell)$ be real affine polynomials, and let $C>0$. Write $S_j(z)$ for the complete homogeneous polynomial of degree $j$ in the $z_i$, and define
--   $$
--   J=4d+10,\qquad A(M,\ell)=C^{-1}\sum_{j=0}^J S_j(z(M,\ell)).
--   $$
--   Then $A$ has total degree at most $J$. At every real pair $(M,\ell)$ for which all $|z_i(M,\ell)|\le1/4$,
--   $$
--   \left|C\prod_{i\in I}(1-z_i(M,\ell))A(M,\ell)-1\right|\le1/100.
--   $$
--   This specifies the polynomial used in the source's reciprocal approximation, allowing its explicit instance in Lemma 3.15 to reuse the geometric truncation estimate. Empty index sets are included.
-- source:
--   Kayal, Sen, Szabó, Near-optimal quantum query lower bounds on bipartiteness and expansion testing in the bounded-degree graph model, held October 2026 manuscript, Appendix A.5, PDF/printed pp. 35–36, equations (A.16)–(A.22); specialization in equation (20), p. 19 and Appendix A.6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open QuantumBipartiteTesting.Bipartiteness Finset

theorem QuantumBipartiteTesting.Bipartiteness.explicit_reciprocal_truncation {I : Type} [Fintype I] (z : I → Bivariate)
    (haffine : ∀ i, (z i).totalDegree ≤ 1) (C : ℝ) (hC : 0 < C) :
    (MvPolynomial.C C⁻¹ * ∑ j ∈ range (4*Fintype.card I+11), Homogeneous z j).totalDegree ≤
      4*Fintype.card I+10 ∧
    ∀ M l : ℝ, (∀ i, |Eval (z i) M l| ≤ 1/4) →
      |Eval (MvPolynomial.C C * ∏ i, (1-z i)) M l *
        Eval (MvPolynomial.C C⁻¹ * ∑ j ∈ range (4*Fintype.card I+11), Homogeneous z j) M l - 1| ≤ 1/100 := by sorry
