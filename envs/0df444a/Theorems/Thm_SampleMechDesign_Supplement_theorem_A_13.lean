-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_theorem_A_13
-- name    : SampleMechDesign.Supplement.theorem_A_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:51:10.253859+00:00
-- url     : https://prove2.me/theorems/b9ca8576-74d3-59df-b346-9ae7733cccba
-- title:
--   Theorem A.13 (corrected: delineability on arrangement cells) — lotteries for $n$ buyers: $\mathcal M'$ is $(\ell(m+1),n((\ell+1)^2+m\ell))$-delineable
-- statement:
--   Let $n$ unit-demand or additive buyers arrive simultaneously and each buy, from one anonymous length-$\ell$ lottery menu, the lottery that maximizes her expected utility, with $n$ units of each item and at most one unit per buyer. Let $\mathcal M'$ be the class of functions $\mathrm{profit}'_M(v,z)=\sum_jp_{v_j}-c(Q)$, where $Q$ is the profile of the bundles $\sum_{i:z_j[i]<\varphi_{v_j}[i]}e_i$. Then
--   $$
--   \mathcal M'\ \text{ is }\ \big(\ell(m+1),\ n\big((\ell+1)^2+m\ell\big)\big)\text{-delineable}.
--   $$
--   The statement is made for every parameter set $P\subseteq\mathbb R^{\ell(m+1)}$, which contains the additive set ($\varphi^{(j)}\in[0,1]^m$) and the unit-demand set ($\sum_i\varphi^{(j)}[i]\le1$), for every cost of the profile of bundles and for every tie-breaking rule of each buyer.
--
--   Differences from the source:
--   - correction: (d, t)-delineable per Definition 3.5 (linear on connected components of P ∖ H) → the published corrected SampleMechDesign.IsDelineable (affine on every cell of the arrangement, faces included); reason: base correction C1: the printed definition makes Theorem 3.9 false; for convex P the two agree off the hyperplanes
--   - generalization: points (v, z) with z ∈ [0, 1]^m → points (v, z) with z ∈ ℝ^m; reason: delineability for every point of a larger domain implies it on [0, 1]^m
--   - reading: the cost function and the tie-breaking rule is not specified → every bundle cost c and every tie-breaking rule among utility-maximizing entries; reason: the paper leaves ties open; within one cell the set of maximizing entries is fixed, so any rule that depends only on it gives the same entry
--   - encoding: parameters (φ^(1..ℓ), p^(1..ℓ)) ∈ ℝ^{ℓ(m+1)} → p : Fin (ℓ*(m+1)) → ℝ via finProdFinEquiv, last coordinate of each block the price; reason: an index bijection; same instances
--   - generalization: the additive or unit-demand lottery parameter set → every parameter set P ⊆ ℝ^{ℓ(m+1)}; reason: delineability is monotone in P, and the buyers' utilities have the same linear form for both buyer types (p.31)
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem A.13, p.31 (PDF p.31); Lemma 3.21, p.14; Definition 3.5, p.10

import Mathlib
import Definitions.Def_SampleMechDesign_IsDelineable
import Definitions.Def_SampleMechDesign_Supplement_multiLotteryProfit

namespace SampleMechDesign.Supplement

/-- **Theorem A.13.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.31. For `n` unit-demand
or additive buyers who choose simultaneously from one anonymous length-`ℓ` lottery menu (`n` units
of each item, at most one unit per buyer), the class `M′` of functions
`profit′_M(v, z) = ∑_j p_{v_j} − c(Q)` is `(ℓ (m + 1), n((ℓ + 1)² + m ℓ))`-delineable.

**Formalization Note.** Delineability is the published corrected Definition 3.5. The statement
is made for every parameter set `P ⊆ ℝ^{ℓ(m+1)}`, which contains both the additive set
(`φ^(j) ∈ [0, 1]^m`) and the unit-demand set (`∑_i φ^(j)[i] ≤ 1`): the buyers' utilities have the
same linear form in both cases (p.31). It holds for every cost `c` of the profile of bundles and
every tie-breaking rule of each buyer; the draws `z_j` range over `ℝ^m`. -/
theorem theorem_A_13 {n ℓ m : ℕ} (P : Set (Fin (ℓ * (m + 1)) → ℝ)) (c : Bundles n m → ℝ)
    (tb : Fin n → (Fin m → ℝ) → Finset (Fin (ℓ + 1)) → Fin (ℓ + 1)) (htb : ∀ j, IsChoice (tb j)) :
    SampleMechDesign.IsDelineable (ℓ * (m + 1)) (n * ((ℓ + 1) ^ 2 + m * ℓ)) P
      (multiLotteryProfit c tb) := by sorry

end SampleMechDesign.Supplement
