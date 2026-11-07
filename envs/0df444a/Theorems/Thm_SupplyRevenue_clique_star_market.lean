-- Prove2me | Theorems.Thm_SupplyRevenue_clique_star_market
-- name    : SupplyRevenue.clique_star_market
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:58.956745+00:00
-- url     : https://prove2.me/theorems/67f50b32-e97b-4a77-8ab7-26e43c016b28
-- title:
--   §9.1 — the clique-star market
-- statement:
--   Let $d\ge 1$. The clique-star market on any $m$ items holding the $\binom{d+1}{2}$ edges of the complete graph has, for every order and $0\le\delta\le 1$,
--
--   $$A_\delta=\frac{\delta(d+1)}{2},\qquad B=\frac{d+1}{2},\qquad\mathrm{OblivItemRev}=\mathrm{FixedItemRev}=\mathrm{SeqItemRev}=1.$$
--
--   It is rational, in $\mathcal V_d$ and in $\mathcal S_d$. Whenever $K\ge 24$ and $d\le K^2$, the market fits: $\binom{d+1}{2}\le m$. It supplies the $d\delta$, $d$, $r\delta$ and $r$ lower bounds of the goal.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: the option chosen from a menu → any utility-maximizing option on supported types, with no payment tie; reason: R6: this makes $B$ larger, hence the upper bound stronger, and the values of §9 are unchanged
--   - reading: "SeqItemRev adapts to sales" → finite mixtures of deterministic policies mapping the list of earlier purchases to an offer; reason: R8: behavioural coins over finitely many histories are such a mixture (Kuhn)
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
--   - reading: "finite rational types", class membership → every mass and value is a rational cast; a class constrains supported types only; reason: R10: unsupported types do not affect any expectation
--   - generalization: items are edges → an injection of the edges into `Fin m`, any $m\ge\binom{d+1}{2}$, with the other items worthless; reason: p.19: "Worthless hidden padding preserves these identities"
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §9.1, pp.18–19; "Unknown complementary structure", p.19

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_BuyMany
import Definitions.Def_SupplyRevenue_Revenue
import Definitions.Def_SupplyRevenue_Families

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§9.1, pp.18–19, and the clique-star sentence of "Unknown complementary structure", p.19: for every order and `0 ≤ δ ≤ 1`,
`A_δ = δ(d+1)/2`, `B = (d+1)/2`, `OblivItemRev = FixedItemRev = SeqItemRev = 1`. "Worthless hidden padding preserves these
identities": `e` places the edges among any `m ≥ C(d+1, 2)` items. The market is rational, in `𝒱_d` and in `𝒮_d`. The second
part is the fit: `K ≥ 24` and `d ≤ K²` give `C(d+1, 2) ≤ m`, and hence a placement `e`.

**Formalization Note** `d` is the demand bound. The market has `n = d + 1` buyers. -/
theorem clique_star_market :
    (∀ {d m : ℕ} (hd : 1 ≤ d) (e : CliqueEdge d ↪ Fin m) (tie : Tie m)
        (π : Equiv.Perm (Fin (d + 1))),
      let D := cliqueMarket e
      (∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → capRev tie D δ = ENNReal.ofReal (δ * ((d : ℝ) + 1) / 2)) ∧
      buyManyRev D = ENNReal.ofReal (((d : ℝ) + 1) / 2) ∧
      oblivRev tie D = 1 ∧ fixedRev tie D π = 1 ∧ seqRev tie D π = 1 ∧
      IsRationalInstance D ∧ InstanceInClass D (InV d) ∧ InstanceInClass D (InS d)) ∧
    (∀ d m : ℕ, 1 ≤ d → 24 ≤ capK m → d ≤ capK m ^ 2 →
      (d + 1).choose 2 ≤ m ∧ Nonempty (CliqueEdge d ↪ Fin m)) := by sorry

end SupplyRevenue
