-- Prove2me | Theorems.Thm_SupplyRevenue_lemma_9_1
-- name    : SupplyRevenue.lemma_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:57.933861+00:00
-- url     : https://prove2.me/theorems/4ef94df9-accb-4016-a6da-f097485c9fac
-- title:
--   Lemma 9.1 — family bounds (18)
-- statement:
--   Consider the family (17) with $L\ge 3$, $k=4^L$, $1\le n\le k$, $2\le t\le L$, $\rho=n/k$, on $m\ge k^2$ items. For every buyer order and residual order,
--
--   $$B=nk(t+1),\qquad A_\rho\ge nk,\qquad\mathrm{SeqItemRev}\le 7\min\{nk,k^2/t\}+6nkt/L.\tag{18}$$
--
--   The family is rational and XOS. It is the source of the $\sqrt{\delta K}$ and $K$ lower bounds.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: the option chosen from a menu → any utility-maximizing option on supported types, with no payment tie; reason: R6: this makes $B$ larger, hence the upper bound stronger, and the values of §9 are unchanged
--   - reading: "SeqItemRev adapts to sales" → finite mixtures of deterministic policies mapping the list of earlier purchases to an offer; reason: R8: behavioural coins over finitely many histories are such a mixture (Kuhn)
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
--   - reading: "finite rational types", class membership → every mass and value is a rational cast; a class constrains supported types only; reason: R10: unsupported types do not affect any expectation
--   - generalization: $m=k^2$ → any $m\ge k^2$, with worthless items outside the $k^2$ active ones; reason: $m=k^2$ is the page's case, and p.18 pads with worthless hidden items
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Lemma 9.1, p.17, (17), (18)

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_BuyMany
import Definitions.Def_SupplyRevenue_Revenue
import Definitions.Def_SupplyRevenue_Families

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Lemma 9.1, p.17, with (18), for the family (17): `L ≥ 3`, `k = 4^L`, `m = k²`, `1 ≤ n ≤ k`, `2 ≤ t ≤ L`, `ρ = n/k`. For every
order and every residual order, `B = nk(t+1)`, `A_ρ ≥ nk`, `SeqItemRev ≤ 7 min{nk, k²/t} + 6nkt/L`. The family is rational
and XOS (p.17).

**Formalization Note** `coreFamily` has `k²` active items among `m ≥ k²`; `m = k²` is the page's instance, and the padding
of p.18 is the other values of `m`. Here `L`, `k`, `t` are the parameters of §9, not those of §2 or §4. -/
theorem lemma_9_1 (L n t m : ℕ) (hL : 3 ≤ L) (hn1 : 1 ≤ n) (hnk : n ≤ 4 ^ L) (ht2 : 2 ≤ t)
    (htL : t ≤ L) (hm : 4 ^ L * 4 ^ L ≤ m) (tie : Tie m)
    (π : Equiv.Perm (Fin n)) :
    let k : ℝ := ((4 ^ L : ℕ) : ℝ)
    let D := coreFamily L n t m (by omega) hm
    buyManyRev D = ENNReal.ofReal ((n : ℝ) * k * ((t : ℝ) + 1)) ∧
    ENNReal.ofReal ((n : ℝ) * k) ≤ capRev tie D ((n : ℝ) / k) ∧
    seqRev tie D π ≤ ENNReal.ofReal
      (7 * min ((n : ℝ) * k) (k ^ 2 / (t : ℝ)) + 6 * (n : ℝ) * k * (t : ℝ) / (L : ℝ)) ∧
    IsRationalInstance D ∧ InstanceInClass D IsXOS := by sorry

end SupplyRevenue
