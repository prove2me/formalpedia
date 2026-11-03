-- Prove2me | Theorems.Thm_RankOneBTF_proposition_6
-- name    : RankOneBTF.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:39.115677+00:00
-- url     : https://prove2.me/theorems/33d07228-2b85-4c2d-bb53-960c1bf0e40f
-- title:
--   Proposition 6 — without corruption, the ground truth is optimal for (sLP), uniquely iff $\bar x,\bar y,\bar z\neq0$
-- statement:
--   Let $n,m,l\ge1$, $\bar x\in\{0,1\}^n$, $\bar y\in\{0,1\}^m$, $\bar z\in\{0,1\}^l$, $\bar{\mathcal W}=\bar x\otimes\bar y\otimes\bar z$, and let the input tensor be $\mathcal G:=\bar{\mathcal W}$. Then:
--
--   1. $(\bar x,\bar y,\bar z,\bar{\mathcal W})$ is an optimal solution of the standard LP (sLP);
--   2. it is the **unique** optimal solution of (sLP) if and only if $\bar x\ne0$, $\bar y\ne0$ and $\bar z\ne0$.
--
--   This settles recovery at $p=0$; since the feasible region of (fLP) lies inside that of (sLP), it also gives the case $p=0$ of Theorem 4.
--
--   Differences from the source:
--   - encoding: x̄, ȳ, z̄ ≠ 0 → each of x̄, ȳ, z̄ has a coordinate equal to 1; reason: a binary vector is nonzero iff it has a one
--   - reading: an n × m × l binary tensor (p.2), dimensions not restated in Proposition 6 → 0 < n, 0 < m, 0 < l; reason: the tensor's dimensions are positive integers; at n = m = l = 0 the variable space is one point, so (x̄, ȳ, z̄, W̄) is trivially the unique optimum while x̄ = 0, and the printed "only if" fails
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §7.1, Proposition 6, p.15

import Mathlib
import Definitions.Def_RankOneBTF_slpRegion

namespace RankOneBTF

/-- **Proposition 6** (arXiv:2202.07053v3, §7.1, p.15): "Let x̄ ∈ {0,1}ⁿ, ȳ ∈ {0,1}ᵐ,
z̄ ∈ {0,1}ˡ. Define W̄ = (w̄_ijk) := x̄ ⊗ ȳ ⊗ z̄ ∈ {0,1}^{n×m×l} and let G := W̄. Then
(x̄, ȳ, z̄, W̄) is an optimal solution of Problem (sLP). Furthermore, (x̄, ȳ, z̄, W̄) is the unique
optimal solution of Problem (sLP) if and only if x̄, ȳ, z̄ ≠ 0."

**Formalization Note** Both clauses are stated: optimality, and uniqueness ⇔ each of `x̄, ȳ, z̄`
has a one. (sLP) is built from the uncorrupted input `G = W̄`. The dimensions of the
`n × m × l` tensor (p.2) are positive (`0 < n, 0 < m, 0 < l`): for `n = m = l = 0` the variable
space is a single point, so the ground truth is trivially the unique optimum while `x̄ = 0`, and
the "only if" fails. -/
theorem proposition_6 {n m l : ℕ} (hn : 0 < n) (hm : 0 < m) (hl : 0 < l)
    (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) :
    IsOptimalOn (slpRegion (groundTruth xb yb zb)) (lpObjective (groundTruth xb yb zb))
        (groundPoint xb yb zb) ∧
      (IsUniqueOptimalOn (slpRegion (groundTruth xb yb zb)) (lpObjective (groundTruth xb yb zb))
          (groundPoint xb yb zb) ↔
        (∃ i, xb i = true) ∧ (∃ j, yb j = true) ∧ (∃ k, zb k = true)) := by sorry

end RankOneBTF
