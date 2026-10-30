-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_triple_product_contraction
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.triple_product_contraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:58:54.416437+00:00
-- url     : https://prove2.me/theorems/9499ec6b-c468-4761-b5d2-f4f34bce341e
-- title:
--   Lemma 8 / Eq.(39): triple-product contraction
-- statement:
--   Let $d,k\ge1$ and $k\le N$. Let $a,b$ be separately injective ordered port lists. With $W(a)=V^{(k)}[(a_k,N+1)\cdots(a_1,N+k)]$, partial transpose on the last $k$ factors, and the recursively constructed collision count $r=\sum_{s=1}^k\mathbf1_{a_s=L_{s-1}\cdots L_1(b_s)}$, one has
--
--   $$W(a)W(b)W(a)=d^{2r}W(a).$$
--
--   The factor order and the exponent twice the collision count are retained. All operators are unnormalized, and cross-list coincidences are allowed.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 10, Lemma 8 / Eq.(39): triple-product contraction

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.10, Lemma 8, Eq.(39): ordered triple product and exponent 2r. -/
theorem triple_product_contraction (d N k : ℕ) (hd : 1 ≤ d)
    (hk : 1 ≤ k) (hNk : k ≤ N) (a b : MPBTPortSelection N k) :
    mpbtWordOperator d N k a * mpbtWordOperator d N k b * mpbtWordOperator d N k a =
      ((d : ℂ)^(2 * collisionCount a b)) • mpbtWordOperator d N k a := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
