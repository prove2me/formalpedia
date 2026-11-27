-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_theorem_A_12
-- name    : SampleMechDesign.Supplement.theorem_A_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:50:10.578849+00:00
-- url     : https://prove2.me/theorems/522223e3-71fe-4b51-99ed-aa9d65c238d0
-- title:
--   Theorem A.12 (corrected: delineability on arrangement cells) — lotteries for a unit-demand buyer: $\mathcal M'$ is $(\ell(m+1),(\ell+1)^2+m\ell)$-delineable
-- statement:
--   Let a single unit-demand buyer face a length-$\ell$ lottery menu, so that each entry satisfies $\varphi^{(j)}\in[0,1]^m$ and $\sum_i\varphi^{(j)}[i]\le1$, and let $\mathcal M'$ be the class of functions $\mathrm{profit}'_M(v,z)=p_v-c\big(\sum_{j:z[j]<\varphi_v[j]}e_j\big)$ of Section 3.4.4. Then
--   $$
--   \mathcal M'\ \text{ is }\ \big(\ell(m+1),\ (\ell+1)^2+m\ell\big)\text{-delineable}.
--   $$
--   That is, for every point $(v,z)$ there are at most $(\ell+1)^2+m\ell$ hyperplanes in the parameter space $\mathbb R^{\ell(m+1)}$ such that $\mathrm{profit}'_M(v,z)$ is affine in the menu parameters on every cell of their arrangement. With Theorem 3.9 this gives generalization guarantees for lottery menus sold to a unit-demand buyer.
--
--   Differences from the source:
--   - correction: (d, t)-delineable per Definition 3.5 (linear on connected components of P ∖ H) → the published corrected SampleMechDesign.IsDelineable (affine on every cell of the arrangement, faces included); reason: base correction C1: the printed definition makes Theorem 3.9 false; for convex P the two agree off the hyperplanes
--   - generalization: points (v, z) with z ∈ [0, 1]^m → points (v, z) with z ∈ ℝ^m; reason: delineability for every point of a larger domain implies it on [0, 1]^m
--   - reading: the cost function and the tie-breaking rule is not specified → every bundle cost c and every tie-breaking rule among utility-maximizing entries; reason: the paper leaves ties open; within one cell the set of maximizing entries is fixed, so any rule that depends only on it gives the same entry
--   - encoding: parameters (φ^(1..ℓ), p^(1..ℓ)) ∈ ℝ^{ℓ(m+1)} → p : Fin (ℓ*(m+1)) → ℝ via finProdFinEquiv, last coordinate of each block the price; reason: an index bijection; same instances
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem A.12, p.31 (PDF p.31); Section 3.4.4, p.14; Definition 3.5, p.10

import Mathlib
import Definitions.Def_SampleMechDesign_IsDelineable
import Definitions.Def_SampleMechDesign_Supplement_Alloc
import Definitions.Def_SampleMechDesign_Supplement_unitDemandLotteryParams

namespace SampleMechDesign.Supplement

/-- **Theorem A.12.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.31. The class `M′` of
Section 3.4.4 (functions `profit′_M(v, z) = p_v − c(∑_{j : z[j] < φ_v[j]} e_j)` of length-`ℓ`
lottery menus) is `(ℓ (m + 1), (ℓ + 1)² + m ℓ)`-delineable, over the parameter set of a
unit-demand buyer: `φ^(j) ∈ [0, 1]^m` and `∑_i φ^(j)[i] ≤ 1`.

**Formalization Note.** Delineability is the published corrected Definition 3.5
(`SampleMechDesign.IsDelineable`: affine on every cell of an arrangement of at most `t`
hyperplanes, faces included). The statement holds for every bundle cost `c` and every
tie-breaking rule `tb` among the buyer's utility-maximizing entries; points `(v, z)` range over
`ℝ^m × ℝ^m`, which contains the paper's `z ∈ [0, 1]^m`. -/
theorem theorem_A_12 {ℓ m : ℕ} (c : Finset (Fin m) → ℝ)
    (tb : (Fin m → ℝ) → Finset (Fin (ℓ + 1)) → Fin (ℓ + 1)) (htb : IsChoice tb) :
    SampleMechDesign.IsDelineable (ℓ * (m + 1)) ((ℓ + 1) ^ 2 + m * ℓ) (unitDemandLotteryParams ℓ m)
      (lotteryProfit c tb) := by sorry

end SampleMechDesign.Supplement
