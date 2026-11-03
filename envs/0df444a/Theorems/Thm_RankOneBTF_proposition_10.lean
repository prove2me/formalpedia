-- Prove2me | Theorems.Thm_RankOneBTF_proposition_10
-- name    : RankOneBTF.proposition_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:25:25.540587+00:00
-- url     : https://prove2.me/theorems/33b5c0fb-4ab5-4cc1-940c-bc520b373b37
-- title:
--   Proposition 10 — deterministic conditions under which the ground truth is optimal for (fLP)
-- statement:
--   Let $\bar x,\bar y,\bar z$ be binary vectors, $\bar{\mathcal W}=\bar x\otimes\bar y\otimes\bar z$, and let $\mathcal G$ be an input tensor with $\mathcal F\ne\emptyset$ (some entry is corrupted). Let $0<\alpha<1$. Suppose that
--
--   1. Condition 1 of Proposition 7 holds: $F^{x,i}>0$ for every $i$ with $\bar x_i=0$, and likewise for $y$ and $z$;
--   2. Conditions 1–3 of Proposition 10 hold (the counts $T^{x,y,i,j}_1$, $T^{y,z,j,k}_1$, $T^{x,z,i,k}_1$ are at least $1$ on ones of the ground truth; $T^{x,i}_{111}\ge\alpha T^{x,i}_{11}\bar T^{y,z}_1$ and its counterparts; inequality (50) and its counterparts);
--   3. Condition 4 holds: for each $(i,j,k)\in\mathcal T\cap\mathcal P$,
--   $$
--   3\bar\gamma_{ijk}\ge\max\Bigl\{\frac{F^{x,i}_{11}}{T^{x,i}_{11}},\frac{F^{y,j}_{11}}{T^{y,j}_{11}},\frac{F^{z,k}_{11}}{T^{z,k}_{11}}\Bigr\}.\qquad(51)
--   $$
--
--   Then $(\bar x,\bar y,\bar z,\bar{\mathcal W})$ is an optimal solution of the flower LP (fLP) for $\mathcal G$.
--
--   It is a dual-certificate condition: under it an explicit dual solution of (fLP) has the objective value of the ground truth.
--
--   Differences from the source:
--   - reading: "Let α < 1 be a constant arbitrarily close to 1" (Condition 2; α also enters γ̄_ijk in Condition 4) → for every α with 0 < α < 1, the same α in Conditions 2 and 4; reason: the conclusion is claimed for any such α; positivity of α is needed for the terms 1/(αT̄) to have the printed sign
--   - encoding: fractions in (50), γ̄_ijk and (51) → real division with a/0 = 0; reason: under the hypotheses every denominator that occurs is positive, so no instance changes
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §8.1, Proposition 10, pp.24–25

import Mathlib
import Definitions.Def_RankOneBTF_flpRegion
import Definitions.Def_RankOneBTF_Prop7Cond1
import Definitions.Def_RankOneBTF_Prop10Cond1
import Definitions.Def_RankOneBTF_gammaBar

namespace RankOneBTF

/-- **Proposition 10** (arXiv:2202.07053v3, §8.1, pp.24–25): "Let x̄ ∈ {0,1}ⁿ, ȳ ∈ {0,1}ᵐ,
z̄ ∈ {0,1}ˡ and define W̄ = (w̄_ijk) := x̄ ⊗ ȳ ⊗ z̄ ∈ {0,1}^{n×m×l}. Suppose that ℱ ≠ ∅. Then
(x̄, ȳ, z̄, W̄) is an optimal solution of Problem (fLP), if in addition to Condition 1 of
Proposition 7, the following conditions are satisfied:" Conditions 1–4 (`Prop10Cond1`,
`Prop10Cond2 α`, `Prop10Cond3` = (50) and counterparts, `Prop10Cond4 α` = (51)).

**Formalization Note** "Let α < 1 be a constant arbitrarily close to 1" (Condition 2) is read
as: for any `α` with `0 < α < 1`, the same `α` in Conditions 2 and 4 (it enters `γ̄_ijk`).
`ℱ ≠ ∅` means some entry of `G` differs from `W̄`. -/
theorem proposition_10 {n m l : ℕ} (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) (hF : ∃ i j k, G i j k ≠ groundTruth xb yb zb i j k)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h7 : Prop7Cond1 xb yb zb G) (h1 : Prop10Cond1 xb yb zb G) (h2 : Prop10Cond2 α xb yb zb G)
    (h3 : Prop10Cond3 xb yb zb G) (h4 : Prop10Cond4 α xb yb zb G) :
    IsOptimalOn (flpRegion G) (lpObjective G) (groundPoint xb yb zb) := by sorry

end RankOneBTF
