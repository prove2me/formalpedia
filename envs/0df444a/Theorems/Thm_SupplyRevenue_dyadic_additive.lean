-- Prove2me | Theorems.Thm_SupplyRevenue_dyadic_additive
-- name    : SupplyRevenue.dyadic_additive
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:43.715205+00:00
-- url     : https://prove2.me/theorems/e3f54ba3-8d4e-42d0-8135-126cef5f3906
-- title:
--   §9.2 — the dyadic additive family: $B=1$ and $A_1=(2-1/m_0)/(L+1)$
-- statement:
--   Let $m_0=2^L\le m$. For the one-buyer dyadic additive family, grand-bundle pricing gives $B=1$, and
--
--   $$\mathrm{OblivItemRev}=A_1=\frac{2-1/m_0}{L+1},$$
--
--   attained by uniform prices $1/m_0$ on the active items. The same value holds for $\mathrm{FixedItemRev}$ and $\mathrm{SeqItemRev}$. The buyer is rational, XOS and in $\mathcal S_1$. This gives a $\Theta(K)$ buy-many separation even from $A_1$.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: the option chosen from a menu → any utility-maximizing option on supported types, with no payment tie; reason: R6: this makes $B$ larger, hence the upper bound stronger, and the values of §9 are unchanged
--   - reading: "SeqItemRev adapts to sales" → finite mixtures of deterministic policies mapping the list of earlier purchases to an offer; reason: R8: behavioural coins over finitely many histories are such a mixture (Kuhn)
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
--   - reading: "finite rational types", class membership → every mass and value is a rational cast; a class constrains supported types only; reason: R10: unsupported types do not affect any expectation
--   - reading: "every vector, assortment and randomization has revenue at most" the value → also $\mathrm{FixedItemRev}$ and $\mathrm{SeqItemRev}$ equal it; reason: both lie between $\mathrm{OblivItemRev}$ and $A_1$ on p.2, and the goal needs them
--   - generalization: $m_0=2^L$ active items → any $m\ge 2^L$ items, the others worthless; reason: p.19: "Pad the largest $2^L\le m$ with worthless items"; $m=2^L$ is the instance
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §9.2, p.19; "Unknown complementary structure", p.19

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_BuyMany
import Definitions.Def_SupplyRevenue_Revenue
import Definitions.Def_SupplyRevenue_Families

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§9.2, p.19, and "Unknown complementary structure", p.19: with `m₀ = 2^L`, `B = 1` and
`OblivItemRev = A₁ = (2 − 1/m₀)/(L + 1)`, attained by uniform prices `1/m₀`, and "every vector, assortment and
randomization has revenue at most" this value, which includes `FixedItemRev` and `SeqItemRev`. The buyer is rational, XOS
and in `𝒮₁`.

**Formalization Note** `m ≥ 2^L`, and the padding items are worthless. The attaining matrix offers the active items at price
`1/m₀`. `L` here is the dyadic height, with `L = 0` allowed. -/
theorem dyadic_additive (L m : ℕ) (hm : 2 ^ L ≤ m) (tie : Tie m) (π : Equiv.Perm (Fin 1)) :
    let D := dyadicFamily L m hm
    let V : ℝ := (2 - 1 / (2 : ℝ) ^ L) / ((L : ℝ) + 1)
    buyManyRev D = 1 ∧
    capRev tie D 1 = ENNReal.ofReal V ∧
    oblivRev tie D = ENNReal.ofReal V ∧
    fixedRev tie D π = ENNReal.ofReal V ∧
    seqRev tie D π = ENNReal.ofReal V ∧
    rev tie D (fun _ => ({ assort := activeItems m (2 ^ L)
                           price := fun _ => 1 / (2 : ℝ) ^ L
                           price_nonneg := fun _ => by positivity } : Offer m)) π = V ∧
    IsRationalInstance D ∧ InstanceInClass D IsXOS ∧ InstanceInClass D (InS 1) := by sorry

end SupplyRevenue
