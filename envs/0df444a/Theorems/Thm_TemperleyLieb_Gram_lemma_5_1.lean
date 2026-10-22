-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_lemma_5_1
-- name    : TemperleyLieb.Gram.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:55.800226+00:00
-- url     : https://prove2.me/theorems/2a86569c-b2e4-4975-ab67-7fafdb38d0d1
-- title:
--   Lemma 5.1, p. 19 — branching law for the Gram determinant
-- statement:
--   Let $\lambda=(f,n-2f)$ with $f\ge1$, and let $\mu=(f-1,n-2f+1)$ be its predecessor shape at level $n-1$. The Gram determinants satisfy
--
--   $$\det(\lambda)=\prod_{\nu\to\lambda}\det(\nu)\left(\frac{p_{n-2f+2}}{p_{n-2f+1}}\right)^{\dim(\mu)}.$$
--
--   When $n>2f$, the predecessors are $(f,n-2f-1)$ and $\mu$; when $n=2f$, only $\mu$ exists. This relation links consecutive levels of the tower and is the immediate recurrence behind the closed product.
--
--   **Formalization Note** Both level-$n$ and level-$(n-1)$ Murphy data are asserted to exist. The statement maps their polynomial Gram determinants to the fraction field for the ratio; the exponent is the number of tableaux of $\mu$ at level $n-1$.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 19, Lemma 5.1

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram
open QAlgorithms.Papers.Independent.Support21.P08

/-- Enyang, Lemma 5.1, p. 19. The two predecessor shapes are displayed
separately so that the missing predecessor at `n=2f` is not manufactured. -/
theorem lemma_5_1 (n : ℕ) (f : Fin (n / 2 + 1)) (hf : 1 ≤ (f : ℕ)) :
    (∃ D : RDatum n, IsMurphyDatum R Polynomial.X n D) ∧
    (∃ D' : RDatum (n - 1), IsMurphyDatum R Polynomial.X (n - 1) D') ∧
      ∀ (D : RDatum n) (D' : RDatum (n - 1)),
        IsMurphyDatum R Polynomial.X n D →
        IsMurphyDatum R Polynomial.X (n - 1) D' →
        (∀ hgap : 2 * (f : ℕ) < n,
          algebraMap R F (gramDet D f) =
            algebraMap R F (gramDet D' ⟨f, by omega⟩) *
            algebraMap R F (gramDet D' ⟨(f : ℕ) - 1, by omega⟩) *
            (algebraMap R F (p (n - 2 * (f : ℕ) + 2)) /
              algebraMap R F (p (n - 2 * (f : ℕ) + 1))) ^
              dimShape (n - 1) ⟨(f : ℕ) - 1, by omega⟩) ∧
        (n = 2 * (f : ℕ) →
          algebraMap R F (gramDet D f) =
            algebraMap R F (gramDet D' ⟨(f : ℕ) - 1, by omega⟩) *
            (algebraMap R F (p (n - 2 * (f : ℕ) + 2)) /
              algebraMap R F (p (n - 2 * (f : ℕ) + 1))) ^
              dimShape (n - 1) ⟨(f : ℕ) - 1, by omega⟩) := by sorry

end TemperleyLieb.Gram
