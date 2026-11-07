-- Prove2me | Theorems.Thm_SupplyRevenue_lemma_2_1
-- name    : SupplyRevenue.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:49.156755+00:00
-- url     : https://prove2.me/theorems/887cc384-c59a-4748-ba5e-eee2edd32322
-- title:
--   Lemma 2.1 — large source payments are recovered by first-sale prices
-- statement:
--   Fix a source meeting aggregate caps $\delta\in(0,1]$, with revenue $R>0$. Let $s_i$ be the full-stock source payment of buyer $i$. Choose $L\ge 4R$, put $H=4mL$ and $R_{\mathrm{high}}=\sum_i E[s_i\mathbf 1\{s_i>H\}]$. Then fresh independent source offers, repriced to $\max\{p_{ij}/2,L\}$ on the same assortments, earn in each fixed order at least
--
--   $$\tfrac{3}{16}R_{\mathrm{high}}.$$
--
--   The substitutions $(L,H)=(4R/\delta,16mR/\delta)$, and $(4\hat R,16m\hat R)$ for $R\le\hat R\le 2R$, are admissible.
--
--   This disposes of the high-payment part of the source in the proof of the upper bounds.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: a source of offers → one finite mixture of offers per buyer; reason: R4: p.2 "finite-mixture approximation"; each offer gives a point of a bounded finite-dimensional set, so arbitrary laws add nothing to the supremum
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Lemma 2.1, p.5; setting of §2, p.5

import Mathlib
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_Revenue

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Lemma 2.1, p.5, under the standing setting of §2: a feasible source of revenue `R > 0` and aggregate cap `δ ≤ 1`.
`L` is the first-sale price (not the level of §9). The admissible substitutions are the last two clauses.

**Formalization Note** "Fresh independent source offers" is `indepE`: one independent draw from `σ i` per buyer, each
offer repriced by `Offer.floorAt L` on the same assortment. `s_i` is the tie-ruled full-stock payment. -/
theorem lemma_2_1 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (tie : Tie m) (D : Instance n m)
    (σ : Source n m) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hσ : FeasibleSource tie D δ σ)
    (hR : 0 < sourceRev tie D σ) :
    let R := sourceRev tie D σ
    (∀ (L H : ℝ), 4 * R ≤ L → H = 4 * (m : ℝ) * L → ∀ π : Equiv.Perm (Fin n),
      3 / 16 * ∑ i, sourceStat tie (D i) (σ i) (fun s => if H < s then s else 0) ≤
        indepE (fun i => (σ i).map fun _ o => o.floorAt L) (fun P => rev tie D P π)) ∧
    (4 * R ≤ 4 * R / δ ∧ 16 * (m : ℝ) * R / δ = 4 * (m : ℝ) * (4 * R / δ)) ∧
    (∀ Rhat : ℝ, R ≤ Rhat → Rhat ≤ 2 * R →
      4 * R ≤ 4 * Rhat ∧ 16 * (m : ℝ) * Rhat = 4 * (m : ℝ) * (4 * Rhat)) := by sorry

end SupplyRevenue
