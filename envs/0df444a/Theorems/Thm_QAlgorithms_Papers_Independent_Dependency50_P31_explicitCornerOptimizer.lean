-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_explicitCornerOptimizer
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.explicitCornerOptimizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:40:34.997005+00:00
-- url     : https://prove2.me/theorems/c5645636-3ccc-4780-94f0-534d345c66c6
-- title:
--   Explicit optimizer for each removable box
-- statement:
--   Let $\nu$ have $N\ge2$ boxes and column lengths $c_1,\ldots,c_{r_1}$, let $d\ge c_1$, and let $u_1,\ldots,u_{c_1}\in\mathbb C^d$ be orthonormal. Fix a removable box $(c_l,l)$ and the standard tableau $t$ with $N$ in that box and the remaining entries in column order. Let $k=\sum_{j<l}c_j$, and let $t_B$ be the suffix tableau obtained by the vertical split before column $l$, translating its columns to start at one and subtracting $k$ from its entries. Define
--
--   $$
--   A=\bigotimes_{j<l}|u_1\wedge\cdots\wedge u_{c_j}\rangle,\qquad
--   B_0=|u_1\wedge\cdots\wedge u_{c_l-1}\rangle
--   \otimes\bigotimes_{j>l}|u_1\wedge\cdots\wedge u_{c_j}\rangle\otimes|u_{c_l}\rangle.
--   $$
--
--   Each wedge is normalized as in (21); an empty wedge or empty left product is the scalar unit. Then
--
--   $$
--   \|P_{t_B}B_0\|>0,\qquad
--   \psi=A\otimes\frac{P_{t_B}B_0}{\|P_{t_B}B_0\|},\qquad
--   \|\psi\|=1,\quad\psi\in\operatorname{Im}P_t,\quad
--   \lambda_1(\psi)^2=\prod_{i=1}^{c_l-1}\left(1-\frac1{h_{(i,l)}}\right).
--   $$
--
--   Thus this specified corner bound is attained. It need not equal the global isotypic optimum when another corner has a larger product.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 18, Proposition 14, equation (62); proof p.19

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Proposition 14, arXiv:1805.00364v2 PDF pp.18-19, equation (62).
PDF inspection confirms P_{t_B} in both numerator and denominator. Nonzero
normalization is a conclusion. The value is for this corner, not the global maximum. -/
theorem explicitCornerOptimizer {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n)
    (t : Filling n) (ht : IsTableau nu.val t) (horder : ColumnOrderedExceptLast t)
    (l : ℕ) (hbox : lastBox t (by omega) = (nu.val.colLen l-1,l))
    (hcorner : Removable nu.val (nu.val.colLen l-1,l))
    (u : ℕ → EuclideanSpace ℂ (Fin d))
    (hu : Orthonormal ℂ (fun i : Fin (nu.val.colLen 0) => u i.val)) :
    ∃ hk : leftSize nu.val l ≤ n,
      0 < ‖optimizerNumerator nu.val t l hk u‖ ∧
      ‖cornerOptimizerState nu.val t l hk u‖ = 1 ∧
      cornerOptimizerState nu.val t l hk u ∈ tableauSpace d t ∧
      largestSchmidtSq (cornerOptimizerState nu.val t l hk u) =
        cornerBound nu.val (nu.val.colLen l-1,l) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
