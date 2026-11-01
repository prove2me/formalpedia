-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_matrix_quotient_bijection
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.matrix_quotient_bijection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:43:11.037768+00:00
-- url     : https://prove2.me/theorems/fc93f787-6015-4cf0-aa4c-534e19421477
-- title:
--   Ordered off-diagonal matrices as coset functions
-- statement:
--   Let $n\ge2$, and let $H\le S_n$ be the subgroup fixing $n$ and $n-1$ individually. For every real zero-diagonal matrix $F$, without a symmetry restriction, the prescription
--
--   $$
--   \widehat F(\mu H)=F_{\mu(n),\mu(n-1)}
--   $$
--
--   is independent of the representative and gives a bijection to real functions on $S_n/H$. Simultaneous inverse permutation of the matrix indices corresponds to left inverse translation of the quotient function:
--
--   $$
--   \widehat{\sigma F}(q)=\widehat F(\sigma^{-1}q).
--   $$
--
--   This identifies the ordered distinct-pair action with $S_n/S_{n-2}$.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 12, Proposition 6 (Appendix A): off-diagonal matrix/quotient bijection

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Proposition 6, source PDF p.12: ordered off-diagonal pairs, no symmetry.
Corrects the representative-subgroup typo S_(n-1) to S_(n-2), as the proof requires. -/
theorem matrix_quotient_bijection (n : ℕ) (hn : 2 ≤ n) :
    Function.Bijective (fun F : DistinctSpace n 2 => quotientValues (finalPoints hn) F.val) ∧
    (∀ (F : DistinctSpace n 2) (s : Perm n),
      quotientValues (finalPoints hn) F.val (Quotient.mk _ s) =
        F.val ![s (finalPoints hn 0), s (finalPoints hn 1)]) ∧
    (∀ (F : DistinctSpace n 2) (s : Perm n) q,
      quotientValues (finalPoints hn) (distinctAction s F).val q =
        quotientValues (finalPoints hn) F.val (cosetTranslate (finalPoints hn) s.symm q)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
