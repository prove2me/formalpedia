-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_theorem3
-- name    : QAlgorithms.Papers.Independent.Next46.P07.theorem3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:53:45.474631+00:00
-- url     : https://prove2.me/theorems/c4f0add3-09e3-4371-ab04-c9a66e3246e8
-- title:
--   Stable rational GL multiplicities as weighted hollow LR tables
-- statement:
--   Let $n>0$, let $r\ge0$, and let $\mu=(\mu_1,\ldots,\mu_r)$ be valid rational $GL(n,\mathbb C)$ weights, with $\mu_i=(\mu_i^+,\mu_i^-)$ a pair of partitions of combined length at most $n$. For a dominant weight $\lambda$, write $F_n^\lambda$ for its irreducible rational module and $\operatorname{LRC}^{\lambda}_{\mu}=\dim_{\mathbb C}\operatorname{Hom}_{GL_n}(F_n^\lambda,\bigotimes_i F_n^{\mu_i})$. For a square matrix of partitions $\Lambda=(\lambda_{ij})$, set $\|\Lambda\|_\mu=\prod_i \operatorname{LRC}^{\mu_i^+}_{\lambda_{i\bullet}}\operatorname{LRC}^{\mu_i^-}_{\lambda_{\bullet i}}$, using polynomial tensor multiplicities. A table is LR if this weight is nonzero and hollow if every diagonal partition is empty. If $n\ge\sum_i(\ell(\mu_i^+)+\ell(\mu_i^-))$, then
--
--   $$\operatorname{LRC}^0_\mu=\sum_{\Lambda\text{ hollow LR with margins }\mu}\|\Lambda\|_\mu.$$
--
--   This gives a weighted combinatorial expression for rational tensor invariants. The sum enumerates actual matrices once inside a finite square bound determined by the margin sizes, including the unique all-empty table for zero margins.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 7, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Theorem 3 (arXiv:2012.06928v1, PDF pp.7-8): the stable-range invariant
multiplicity is the complete finite weighted sum over hollow LR tables. -/
theorem theorem3 (n r : ℕ) (hn : 0 < n) (mu : Fin r → RationalLabel)
    (hmu : ∀ i, RationalLabelFits n (mu i))
    (hstable : (∑ i, ((mu i).1.colLen 0 + (mu i).2.colLen 0)) ≤ n) :
    rationalLRC n (⊥, ⊥) mu = hollowLRSum mu := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
