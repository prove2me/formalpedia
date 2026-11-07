-- Prove2me | Theorems.Thm_SupplyRevenue_closing_tightness
-- name    : SupplyRevenue.closing_tightness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:54.040286+00:00
-- url     : https://prove2.me/theorems/9746cc62-3408-49da-a7e8-cdf9598869bf
-- title:
--   Closing headline tightness — the padded family, the rare item and the buy-many gap
-- statement:
--   1. Let $0<\delta\le 1$ and $\delta L\ge 16$, $k=4^L$, $n=\lfloor\delta k\rfloor$, $\rho=n/k$, $t=\lceil\sqrt{L/\rho}\rceil$. Then $\delta/2\le\rho\le\delta$, $t\in[2,L]$, and on $m\ge 16^L$ items $A_\delta\ge A_\rho\ge nk$, with
--   $$\frac{\mathrm{SeqItemRev}}{nk}\le\frac{7}{\rho t}+\frac{6t}{L}\le\frac{19}{\sqrt{\rho L}}.$$
--   2. A single buyer valuing one item at one with rational probability $0<q\le\delta\le1$ has $A_\delta=\mathrm{FixedItemRev}=\mathrm{OblivItemRev}=q$, on any $m\ge 1$. This instance is rational, XOS and in $\mathcal S_1$.
--   3. For $L\ge 3$, $n=k$, $t=\lceil\sqrt L\rceil$: $B=k^2(t+1)$ and $\mathrm{SeqItemRev}\le 19k^2/\sqrt L$.
--   4. If $16^L\le m<16^{L+1}$ then $4L+2\le K\le 4L+6$.
--
--   Together with the benchmark chain, these give the $\sqrt{\delta K}$ and $K$ tightness clauses.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: the option chosen from a menu → any utility-maximizing option on supported types, with no payment tie; reason: R6: this makes $B$ larger, hence the upper bound stronger, and the values of §9 are unchanged
--   - reading: "SeqItemRev adapts to sales" → finite mixtures of deterministic policies mapping the list of earlier purchases to an offer; reason: R8: behavioural coins over finitely many histories are such a mixture (Kuhn)
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
--   - reading: $\mathrm{SeqItemRev}=O(k^2/\sqrt L)$ → the explicit bound $19k^2/\sqrt L$; reason: it follows from (18) with $t=\lceil\sqrt L\rceil$
--   - reading: "log(16^L) = Θ(log m)" → $4L+2\le K\le 4L+6$ for $16^L\le m<16^{L+1}$; reason: the explicit form, for "the largest $16^L\le m$"
--   - generalization: "For m = 16^L" and the one-item example → the family on any $m\ge 16^L$ items and the rare item on any $m\ge 1$ items, all other items worthless; reason: p.18 pads with worthless hidden items ("the all-policy bound on active items is unchanged"); $m=16^L$ and $m=1$ are instances
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §9, "Closing headline tightness", p.18

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_BuyMany
import Definitions.Def_SupplyRevenue_Revenue
import Definitions.Def_SupplyRevenue_Families

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
"Closing headline tightness", p.18.

1. For `m ≥ 16^L`, `δL ≥ 16`: `n = ⌊δk⌋`, `δ/2 ≤ ρ ≤ δ`, `t = ⌈√(L/ρ)⌉ ∈ [2, L]`, `A_δ ≥ A_ρ ≥ nk`, and
   `SeqItemRev/(nk) ≤ 7/(ρt) + 6t/L ≤ 19/√(ρL)`.
2. The rare item with rational `0 < q ≤ δ` has `A_δ = FixedItemRev = OblivItemRev = q`, on every `m ≥ 1`.
3. `n = k`, `t = ⌈√L⌉`: `B = k²(t+1)` and `SeqItemRev = O(k²/√L)`, with `O` pinned to `19 k²/√L` from (18).
4. `16^L ≤ m < 16^(L+1)` has `4L + 2 ≤ K ≤ 4L + 6`: this is `log(16^L) = Θ(log m)`.

**Formalization Note** `m ≥ 16^L` is written `4^L * 4^L ≤ m`, and all values read only the active items (padding). The
binder `1 ≤ L` is implied by the other hypotheses in clause 1. `n`, `ρ`, `t` are computed by `Nat.floor`, real division
and `Nat.ceil`. The ratios `Ω(√(δL))`, `Ω(L)` are consequences of these bounds. -/
theorem closing_tightness :
    (∀ (L m : ℕ) (δ : ℝ), 1 ≤ L → 0 < δ → δ ≤ 1 → 16 ≤ δ * (L : ℝ) →
      let k : ℝ := ((4 ^ L : ℕ) : ℝ)
      let n : ℕ := ⌊δ * k⌋₊
      let ρ : ℝ := (n : ℝ) / k
      let t : ℕ := ⌈Real.sqrt ((L : ℝ) / ρ)⌉₊
      1 ≤ n ∧ n ≤ 4 ^ L ∧ δ / 2 ≤ ρ ∧ ρ ≤ δ ∧ 2 ≤ t ∧ t ≤ L ∧
      7 / (ρ * (t : ℝ)) + 6 * (t : ℝ) / (L : ℝ) ≤ 19 / Real.sqrt (ρ * (L : ℝ)) ∧
      ∀ (hL : 1 ≤ L) (hm : 4 ^ L * 4 ^ L ≤ m) (tie : Tie m) (π : Equiv.Perm (Fin n)),
        let D := coreFamily L n t m hL hm
        capRev tie D ρ ≤ capRev tie D δ ∧
        ENNReal.ofReal ((n : ℝ) * k) ≤ capRev tie D ρ ∧
        seqRev tie D π ≤ ENNReal.ofReal
          ((7 / (ρ * (t : ℝ)) + 6 * (t : ℝ) / (L : ℝ)) * ((n : ℝ) * k))) ∧
    (∀ (m : ℕ) (hm : 0 < m) (q : ℚ) (h0 : (0 : ℝ) ≤ (q : ℝ)) (h1 : (q : ℝ) ≤ 1) (δ : ℝ),
      0 < q → (q : ℝ) ≤ δ → δ ≤ 1 → ∀ (tie : Tie m) (π : Equiv.Perm (Fin 1)),
        let D := rareItem m hm (q : ℝ) h0 h1
        capRev tie D δ = ENNReal.ofReal (q : ℝ) ∧
        fixedRev tie D π = ENNReal.ofReal (q : ℝ) ∧
        oblivRev tie D = ENNReal.ofReal (q : ℝ) ∧
        IsRationalInstance D ∧ InstanceInClass D IsXOS ∧ InstanceInClass D (InS 1)) ∧
    (∀ (L m : ℕ) (hL3 : 3 ≤ L) (hm : 4 ^ L * 4 ^ L ≤ m) (tie : Tie m)
        (π : Equiv.Perm (Fin (4 ^ L))),
      let k : ℝ := ((4 ^ L : ℕ) : ℝ)
      let t : ℕ := ⌈Real.sqrt (L : ℝ)⌉₊
      let D := coreFamily L (4 ^ L) t m (by omega) hm
      2 ≤ t ∧ t ≤ L ∧
      buyManyRev D = ENNReal.ofReal (k ^ 2 * ((t : ℝ) + 1)) ∧
      seqRev tie D π ≤ ENNReal.ofReal (19 * k ^ 2 / Real.sqrt (L : ℝ))) ∧
    (∀ L m : ℕ, 16 ^ L ≤ m → m < 16 ^ (L + 1) → 4 * L + 2 ≤ capK m ∧ capK m ≤ 4 * L + 6) := by sorry

end SupplyRevenue
