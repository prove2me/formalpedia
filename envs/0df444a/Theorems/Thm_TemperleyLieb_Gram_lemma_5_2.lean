-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_lemma_5_2
-- name    : TemperleyLieb.Gram.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:45.010698+00:00
-- url     : https://prove2.me/theorems/97dc41ce-c25f-423c-8842-583de0bd877f
-- title:
--   Lemma 5.2, p. 20 — closed Gram determinant product
-- statement:
--   Let $\lambda=(f,n-2f)$ be a shape for $n\ge1$, and let $\det(\lambda)$ be the Gram determinant of its Murphy cell module. If $n>2f$, then
--
--   $$\det(\lambda)=\prod_{i=1}^{f}\left(\frac{p_{n-2f+i+1}}{p_i}\right)^{\dim(f-i,n-2f+2i)}.$$
--
--   If $n=2f$, its predecessor is $\mu=(f-1,1)$ at level $n-1$ and
--
--   $$\det(\lambda)=\det(\mu)\,x^{\dim(\lambda)}.$$
--
--   This is the paper's closed formula for the cell-module Gram determinants. The case $f=0$ in the first formula is an empty product, equal to one.
--
--   **Formalization Note** The paper prints the product direction $\mu\triangleright\lambda$, but its factor denominator and proof require $\lambda\triangleright\mu$; the displayed finite product uses the corrected direction. The zero-strand algebra is excluded because the printed even-case predecessor would have cup count $-1$. The theorem asserts existence of the integral Murphy datum, and in the even case of the predecessor datum, so neither case holds merely because such a datum is absent. Division is in $F=\operatorname{Frac}(\mathbb Z[x])$, while the even-case identity is in $R$.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 20, Lemma 5.2 and definition of g_{lambda,mu}

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram
open QAlgorithms.Papers.Independent.Support21.P08
open scoped BigOperators

/-- Enyang, Lemma 5.2, p. 20. The product direction is corrected to
`λ ▷ μ` as in the proof, and the zero-strand algebra is excluded. -/
theorem lemma_5_2 (n : ℕ) (hn : 1 ≤ n) (f : Fin (n / 2 + 1)) :
    (∃ D : RDatum n, IsMurphyDatum R Polynomial.X n D) ∧
    ∀ D : RDatum n, IsMurphyDatum R Polynomial.X n D →
      (2 * (f : ℕ) < n →
        algebraMap R F (gramDet D f) =
          ∏ i ∈ Finset.Icc 1 (f : ℕ),
            (algebraMap R F (p (n - 2 * (f : ℕ) + i + 1)) /
              algebraMap R F (p i)) ^
              dimShape n ⟨(f : ℕ) - i, by omega⟩) ∧
      (n = 2 * (f : ℕ) →
        (∃ D' : RDatum (n - 1), IsMurphyDatum R Polynomial.X (n - 1) D') ∧
        ∀ D' : RDatum (n - 1), IsMurphyDatum R Polynomial.X (n - 1) D' →
          gramDet D f =
            gramDet D' ⟨(f : ℕ) - 1, by omega⟩ *
              Polynomial.X ^ dimShape n f) := by sorry

end TemperleyLieb.Gram
