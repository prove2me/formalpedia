-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_invariantReduction
-- name    : QAlgorithms.Papers.Independent.Next46.P07.invariantReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:54:35.005971+00:00
-- url     : https://prove2.me/theorems/b0f79e6e-aef7-44bc-8d11-64b1fa73ba0b
-- title:
--   Reduction of rational tensor multiplicities to invariants
-- statement:
--   Let $n>0$ and let $\lambda=(\lambda^+,\lambda^-)$ and $\mu_i=(\mu_i^+,\mu_i^-)$, $1\le i\le r$, be valid rational highest weights of $GL(n,\mathbb C)$. Each pair has combined partition length at most $n$. Define $\operatorname{LRC}^{\lambda}_{\mu}$ as the complex dimension of the equivariant Hom space from the irreducible $F_n^\lambda$ to the diagonal tensor product $\bigotimes_iF_n^{\mu_i}$. At this same rank,
--
--   $$\operatorname{LRC}^{\lambda}_{\mu}=\operatorname{LRC}^{0}_{((\lambda^-,\lambda^+),\mu_1,\ldots,\mu_r)}.$$
--
--   The prepended factor is the dual representation of $F_n^\lambda$. This reduction identifies a general multiplicity with an invariant dimension and needs no stable-range hypothesis.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 3, invariant-reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Invariant reduction (arXiv:2012.06928v1, PDF pp.3-4): prepend the dual
label at the same rank; there is no stable-range assumption. -/
theorem invariantReduction (n r : ℕ) (hn : 0 < n) (lambda : RationalLabel)
    (mu : Fin r → RationalLabel) (hlambda : RationalLabelFits n lambda)
    (hmu : ∀ i, RationalLabelFits n (mu i)) :
    rationalLRC n lambda mu =
      rationalLRC n (⊥, ⊥) (Fin.cons (lambda.2, lambda.1) mu) := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
