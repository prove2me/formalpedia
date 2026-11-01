-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_vector_quotient_bijection
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.vector_quotient_bijection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:42:31.722538+00:00
-- url     : https://prove2.me/theorems/b7b38ff0-47a4-410a-9a95-3655fce68216
-- title:
--   Vectors as functions on left cosets
-- statement:
--   Let $n\ge1$ and let $H\le S_n$ be the full subgroup fixing the distinguished point $n$. For $f\in\mathbb R^n$, the representative prescription
--
--   $$
--   \widehat f(\mu H)=f_{\mu(n)}
--   $$
--
--   is independent of the representative and defines a bijection $\mathbb R^n\to\mathbb R^{S_n/H}$. Under the first-order inverse permutation action,
--
--   $$
--   \widehat{\sigma f}(q)=\widehat f(\sigma^{-1}q).
--   $$
--
--   This identifies the first-order activation space with the left-coset function model. In zero-based indexing the distinguished point is $n-1$.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 12, Proposition 5 (Appendix A): vector/quotient bijection

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Proposition 5, source PDF p.12: vectors and left S_n/S_(n-1) cosets.
The representative identity explicitly includes well-definedness of the formula. -/
theorem vector_quotient_bijection (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (vectorValues hn) ∧
    (∀ f (s : Perm n), vectorValues hn f (Quotient.mk _ s) =
      f (s (finalPoints hn 0))) ∧
    (∀ f (s : Perm n) q,
      vectorValues hn (fun i => f (s.symm i)) q =
        vectorValues hn f (cosetTranslate (finalPoints hn) s.symm q)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
