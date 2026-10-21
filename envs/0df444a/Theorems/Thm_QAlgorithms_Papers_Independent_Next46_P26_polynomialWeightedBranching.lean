-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_polynomialWeightedBranching
-- name    : QAlgorithms.Papers.Independent.Next46.P26.polynomialWeightedBranching
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:07:48.079974+00:00
-- url     : https://prove2.me/theorems/965cbe4d-df0b-44af-8767-85064fe047c6
-- title:
--   Polynomial weighted branching
-- statement:
--   Let $\lambda$ be a finite Young diagram with formal independent row variables $x_i$ and column variables $y_j$ over $\mathbb Q$. Let $C[\lambda]$ be its occupied corners and set $D_{rs}=\{(i,j)\in[\lambda]\setminus C[\lambda]:i\ne r,\ j\ne s\}$. Define
--   $$
--   L_{ij}=\sum_{k=i+1}^{\lambda'_j}x_k+\sum_{l=j+1}^{\lambda_i}y_l,\quad R_{irs}=\sum_{k=i+1}^r x_k+\sum_{l=s+1}^{\lambda_i}y_l,\quad T_{jrs}=\sum_{k=r+1}^{\lambda'_j}x_k+\sum_{l=j+1}^s y_l.
--   $$
--   Then the following equality holds in the polynomial ring on these tagged row and column variables:
--   $$
--   \left(\sum_{(p,q)\in[\lambda]}x_py_q\right)\prod_{(i,j)\in[\lambda]\setminus C[\lambda]}L_{ij}
--   =\sum_{(r,s)\in C[\lambda]}x_ry_s\left(\prod_{(i,j)\in D_{rs}}L_{ij}\right)\left(\prod_{i=1}^{r-1}(x_i+R_{irs})\right)\left(\prod_{j=1}^{s-1}(y_j+T_{jrs})\right).
--   $$
--   This is the polynomial form of weighted branching, and setting all weights to one recovers equation (3). For the empty shape it reads $0=0$.
-- source:
--   The weighted hook length formula, arXiv:1006.0043v1, PDF p. 4, Equation (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Equation (4), p.4: the polynomial weighted branching identity.
At the empty diagram both sides are zero. -/
theorem polynomialWeightedBranching (lam : YoungDiagram) :
    totalWeight lam (polyX lam) (polyY lam) *
      (∏ z ∈ noncorners lam, strictHook lam (polyX lam) (polyY lam) z.1 z.2) =
    ∑ z ∈ corners lam, polynomialTerm lam z.1 z.2 := by sorry

end QAlgorithms.Papers.Independent.Next46.P26

end
