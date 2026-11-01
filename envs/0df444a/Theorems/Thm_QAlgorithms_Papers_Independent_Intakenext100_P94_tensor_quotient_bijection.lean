-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_tensor_quotient_bijection
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.tensor_quotient_bijection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:43:31.062974+00:00
-- url     : https://prove2.me/theorems/5477de94-a968-46dc-8bb2-b4f659cd9b23
-- title:
--   Distinct-index tensors as coset functions
-- statement:
--   Let $1\le k\le n$. Consider real order-$k$ tensors $F$ that vanish unless all $k$ indices are pairwise distinct. Let $H\le S_n$ fix the final $k$ distinguished points individually. Then
--
--   $$
--   \widehat F(\mu H)=F_{\mu(n),\mu(n-1),\ldots,\mu(n-k+1)}
--   $$
--
--   is well defined and is a bijection from these tensors to real functions on $S_n/H$. Under simultaneous inverse permutation of all tensor indices,
--
--   $$
--   \widehat{\sigma F}(q)=\widehat F(\sigma^{-1}q).
--   $$
--
--   This is the homogeneous-space realization of the ordered distinct-index action. At $k=n$ the stabilizer is trivial. The zero-order case is outside this statement.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 12, Proposition 7 (Appendix A): distinct-index tensor/quotient bijection

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Proposition 7, source PDF p.12, including k=n and excluding the unstated k=0. -/
theorem tensor_quotient_bijection (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Function.Bijective (fun F : DistinctSpace n k => quotientValues (finalPoints hkn) F.val) ∧
    (∀ (F : DistinctSpace n k) (s : Perm n),
      quotientValues (finalPoints hkn) F.val (Quotient.mk _ s) =
        F.val (fun a => s (finalPoints hkn a))) ∧
    (∀ (F : DistinctSpace n k) (s : Perm n) q,
      quotientValues (finalPoints hkn) (distinctAction s F).val q =
        quotientValues (finalPoints hkn) F.val (cosetTranslate (finalPoints hkn) s.symm q)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
