-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_partially_transposed_product
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.partially_transposed_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:58:31.706545+00:00
-- url     : https://prove2.me/theorems/45f073d4-03b6-452f-aed8-92edabf6e2e8
-- title:
--   Lemma 7 / Eq.(38): product of partially transposed permutation words
-- statement:
--   Let $d,k\ge1$, $k\le N$, and let $a,b$ be separately injective ordered $k$-tuples in $\{1,\ldots,N\}$. On $(\mathbb C^d)^{\otimes(N+k)}$, let $V$ permute tensor factors by inverse-index action and let $W(a)=V^{(k)}[(a_k,N+1)\cdots(a_1,N+k)]$, where the last $k$ factors are transposed. Define $P_s=L_s\cdots L_1$ by Notation 5 and $r=\sum_{s=1}^k\mathbf1_{a_s=P_{s-1}(b_s)}$. Then
--
--   $$W(a)W(b)=d^r V(P_k)W(b).$$
--
--   The port permutation fixes the last $k$ factors and multiplies on the left. These are unnormalized words; partial transpose is not used as a representation homomorphism.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 10, Lemma 7 / Eq.(38): product of partially transposed permutation words

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.10, Lemma 7, Eq.(38): unnormalized words, scalar d^r, left permutation. -/
theorem partially_transposed_product (d N k : ℕ) (hd : 1 ≤ d)
    (hk : 1 ≤ k) (hNk : k ≤ N) (a b : MPBTPortSelection N k) :
    mpbtWordOperator d N k a * mpbtWordOperator d N k b =
      ((d : ℂ)^collisionCount a b) •
        (portAction d N k (accumulated a b k) * mpbtWordOperator d N k b) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
