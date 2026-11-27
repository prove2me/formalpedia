-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_lemma_3_21
-- name    : SampleMechDesign.Supplement.lemma_3_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:50:37.332829+00:00
-- url     : https://prove2.me/theorems/77b20b6a-18cd-57d1-9ed9-38af35d7a4c4
-- title:
--   Lemma 3.21 (corrected: delineability on arrangement cells) — lotteries for one additive buyer: $\mathcal M'$ is $(\ell(m+1),(\ell+1)^2+m\ell)$-delineable
-- statement:
--   Let a single additive buyer face a length-$\ell$ lottery menu, with menu parameters ranging over any set $P\subseteq\mathbb R^{\ell(m+1)}$ (for instance $\varphi^{(j)}\in[0,1]^m$ and arbitrary prices, or all of $\mathbb R^{\ell(m+1)}$), and let $\mathcal M'$ be the class of functions $\mathrm{profit}'_M(v,z)=p_v-c\big(\sum_{j:z[j]<\varphi_v[j]}e_j\big)$ of Section 3.4.4. Then
--   $$
--   \mathcal M'\ \text{ is }\ \big(\ell(m+1),\ (\ell+1)^2+m\ell\big)\text{-delineable}.
--   $$
--   The buyer's chosen entry is determined by the hyperplanes comparing the utilities of two entries, and the bundle $\sum_{j:z[j]<\varphi_v[j]}e_j$ by the hyperplanes $z[j]=\varphi^{(k)}[j]$. Theorem A.13 is derived from this lemma.
--
--   Differences from the source:
--   - correction: (d, t)-delineable per Definition 3.5 (linear on connected components of P ∖ H) → the published corrected SampleMechDesign.IsDelineable (affine on every cell of the arrangement, faces included); reason: base correction C1: the printed definition makes Theorem 3.9 false; for convex P the two agree off the hyperplanes
--   - generalization: points (v, z) with z ∈ [0, 1]^m → points (v, z) with z ∈ ℝ^m; reason: delineability for every point of a larger domain implies it on [0, 1]^m
--   - reading: the cost function and the tie-breaking rule is not specified → every bundle cost c and every tie-breaking rule among utility-maximizing entries; reason: the paper leaves ties open; within one cell the set of maximizing entries is fixed, so any rule that depends only on it gives the same entry
--   - encoding: parameters (φ^(1..ℓ), p^(1..ℓ)) ∈ ℝ^{ℓ(m+1)} → p : Fin (ℓ*(m+1)) → ℝ via finProdFinEquiv, last coordinate of each block the price; reason: an index bijection; same instances
--   - generalization: menus {(φ^(j), p^(j))} ⊆ ℝ^m × ℝ (φ^(j) the item probabilities) → every parameter set P ⊆ ℝ^{ℓ(m+1)}; reason: delineability is monotone in P, so P = ℝ^{ℓ(m+1)} and P = [0,1]^{m} probabilities with real prices are both instances
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Lemma 3.21, p.14 (PDF p.14); Definition 3.5, p.10

import Mathlib
import Definitions.Def_SampleMechDesign_IsDelineable
import Definitions.Def_SampleMechDesign_Supplement_Alloc
import Definitions.Def_SampleMechDesign_Supplement_lotteryProfit

namespace SampleMechDesign.Supplement

/-- **Lemma 3.21.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.14. The class `M′` of
Section 3.4.4 (functions `profit′_M(v, z) = p_v − c(∑_{j : z[j] < φ_v[j]} e_j)` of length-`ℓ`
lottery menus) is `(ℓ (m + 1), (ℓ + 1)² + m ℓ)`-delineable for a single additive buyer.

**Formalization Note.** Delineability is the published corrected Definition 3.5
(`SampleMechDesign.IsDelineable`: affine on every cell of an arrangement of at most `t`
hyperplanes, faces included). The statement holds for every bundle cost `c` and every
tie-breaking rule `tb` among the buyer's utility-maximizing entries; points `(v, z)` range over
`ℝ^m × ℝ^m`, which contains the paper's `z ∈ [0, 1]^m`. The statement is made for every
parameter set `P ⊆ ℝ^{ℓ(m+1)}`: the paper's menus are subsets of `ℝ^m × ℝ` (p.14), and
`P = lotteryParams ℓ m` (every `φ^(j) ∈ [0, 1]^m`, the probabilities of a lottery) and `P = ℝ^{ℓ(m+1)}`
are both instances. -/
theorem lemma_3_21 {ℓ m : ℕ} (P : Set (Fin (ℓ * (m + 1)) → ℝ)) (c : Finset (Fin m) → ℝ)
    (tb : (Fin m → ℝ) → Finset (Fin (ℓ + 1)) → Fin (ℓ + 1)) (htb : IsChoice tb) :
    SampleMechDesign.IsDelineable (ℓ * (m + 1)) ((ℓ + 1) ^ 2 + m * ℓ) P
      (lotteryProfit c tb) := by sorry

end SampleMechDesign.Supplement
