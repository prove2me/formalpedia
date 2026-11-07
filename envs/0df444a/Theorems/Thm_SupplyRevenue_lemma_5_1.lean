-- Prove2me | Theorems.Thm_SupplyRevenue_lemma_5_1
-- name    : SupplyRevenue.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:32.039206+00:00
-- url     : https://prove2.me/theorems/afdf208c-700c-47eb-9432-fd46fabd27b2
-- title:
--   Lemma 5.1 — local caps imply uniform revenue
-- statement:
--   Let $D$ be an independent finite instance, $0<\eta<1$, $b_{ij}\ge 0$, $t_i\in\mathbb R$, and $\sum_i b_{ij}<\eta$ for each item. Suppose every stock law $\mu$ with item survival at least $1-\eta$ admits, for buyer $i$ and every $\varepsilon>0$, a finite mixture of full offers with revenue at least $t_i-\varepsilon$ and unconditional allocation at most $b_{ij}$. Then
--
--   $$\mathrm{OblivItemRev}(D)\ge\sum_i t_i,$$
--
--   and for every $\varepsilon>0$ one finite mixture of price matrices has expected revenue at least $\sum_i t_i-\varepsilon$ for each fixed permutation.
--
--   This removes knowledge of the order, and it is where a fixed point and minimax enter.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Lemma 5.1, p.10

import Mathlib
import Definitions.Def_SupplyRevenue_Revenue
import Definitions.Def_SupplyRevenue_Local

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Lemma 5.1, p.10 (Local caps imply uniform revenue).

**Formalization Note** `t i` is buyer `i`'s target and may be negative, so the first conclusion is `ofReal (Σ_i t_i)`, not a
sum of truncated targets. The local mixture may depend on the stock law, buyer and `ε`. Allocation is unconditional,
over stock, offer and type. The second conclusion is the mixture of matrices with its guarantee per fixed order.
-/
theorem lemma_5_1 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (tie : Tie m) (D : Instance n m)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (b : Fin n → Fin m → ℝ) (hb : ∀ i j, 0 ≤ b i j)
    (t : Fin n → ℝ) (hsum : ∀ j, ∑ i, b i j < η)
    (hlocal : ∀ μ : Lottery m, GoodStock μ η → ∀ i, ∀ ε : ℝ, 0 < ε →
      ∃ τ : Mix (Offer m), t i - ε ≤ localRev tie (D i) τ μ ∧
        ∀ j, localAlloc tie (D i) τ μ j ≤ b i j) :
    ENNReal.ofReal (∑ i, t i) ≤ oblivRev tie D ∧
    ∀ ε : ℝ, 0 < ε → ∃ mixture : Mix (Matrix' n m), ∀ π : Equiv.Perm (Fin n),
      ∑ i, t i - ε ≤ mixture.E fun P => rev tie D P π := by sorry

end SupplyRevenue
