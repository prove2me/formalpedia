-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_word_product_trace
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.word_product_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:59:41.119604+00:00
-- url     : https://prove2.me/theorems/68775800-11d3-44f6-a69b-473192c74cc7
-- title:
--   Corollary 9 / Eq.(40): trace of a product
-- statement:
--   For $d,k\ge1$, $k\le N$, and separately injective ordered port lists $a,b$, let $W(a),W(b)$ be the unnormalized permutation words partially transposed on the last $k$ of $N+k$ factors. Define $r$ using Notation 5 as the number of equalities $a_s=L_{s-1}\cdots L_1(b_s)$. Then
--
--   $$\operatorname{Tr}(W(a)W(b))=d^{N-k}d^{2r}.$$
--
--   Here $N-k=n-2k$. The prefactor is required by the trace on the full tensor space; it disappears only after explicitly applying signal normalization.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 10, Corollary 9 / Eq.(40): trace of a product

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.10, Corollary 9, Eq.(40): the factor d^(n-2k)=d^(N-k) is retained. -/
theorem word_product_trace (d N k : ℕ) (hd : 1 ≤ d)
    (hk : 1 ≤ k) (hNk : k ≤ N) (a b : MPBTPortSelection N k) :
    (mpbtWordOperator d N k a * mpbtWordOperator d N k b).trace =
      (d : ℂ)^(N-k) * (d : ℂ)^(2 * collisionCount a b) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
