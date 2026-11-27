-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_theorem_A_17
-- name    : SampleMechDesign.Supplement.theorem_A_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:53:52.915523+00:00
-- url     : https://prove2.me/theorems/ad4a6486-1985-5609-aaea-c625ad9b71d9
-- title:
--   Theorem A.17 — $n^m-n$ additive valuations that λ-auctions separate: profit $0$ off $H$, at least $2-2\beta$ on $H$
-- statement:
--   For any $n,m\ge2$ and any $\beta\in(0,1)$ there is a set of $N=n^m-n$ distinct $n$-bidder, $m$-item additive valuation vectors $V=\{v^1,\dots,v^N\}$ such that for any $H\subseteq V$ there is a λ-auction $M_H$ with
--   $$
--   \mathrm{profit}_{M_H}(v^i)=0\ \text{ if } v^i\notin H,\qquad \mathrm{profit}_{M_H}(v^i)\ \ge\ 2-2\beta\ \text{ if } v^i\in H .
--   $$
--   The cost is zero, and the statement holds for every tie-breaking rule. This separation property is what drives the sample-complexity lower bound for AMAs and λ-auctions (Theorems A.16 and A.20).
--
--   Differences from the source:
--   - reading: the cost function (general unless noted) → zero cost; reason: the construction uses zero cost (Lemmas A.18–A.19 omit c); the paper gives no argument for other cost functions
--   - reading: the tie-breaking rule is not specified → every tie-breaking rule; reason: the paper leaves ties open; the constructed auctions have unique welfare maximizers
--   - encoding: a set V of N valuation functions and subsets H ⊆ V → an injective N-tuple V and sets H of its indices; reason: same instances
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem A.17, p.34 (PDF p.34); proof pp.34–36

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_amaProfit

namespace SampleMechDesign.Supplement

/-- **Theorem A.17.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.34. For any `n, m ≥ 2`
and any `β ∈ (0, 1)` there is a set of `N = n^m − n` distinct `n`-bidder, `m`-item additive
valuation vectors `V = {v^1, …, v^N}` such that for any `H ⊆ V` there is a λ-auction `M_H` with
profit `0` on `v^i` if `v^i ∉ H` and profit at least `2 − 2β` on `v^i` otherwise.

**Formalization Note.** A λ-auction is an AMA with all weights `1` and boosts `λ ≥ 0`. Zero
cost, as in the construction (Lemmas A.18–A.19 omit the cost). `V` is an injective
`N`-tuple and `H` a set of its indices. The statement holds for every tie-breaking rule `tb`. -/
theorem theorem_A_17 {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (tb : BVal n m → Finset (Alloc n m) → Alloc n m) (htb : IsChoice tb) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ V : Fin (n ^ m - n) → AVal n m, Function.Injective V ∧
      ∀ H : Set (Fin (n ^ m - n)), ∃ lam : Alloc n m → ℝ, (∀ Q, 0 ≤ lam Q) ∧
        ∀ i, (i ∉ H → amaProfit (fun _ => 0) tb (fun _ => 1) lam (additiveVal (V i)) = 0) ∧
          (i ∈ H → 2 - 2 * β ≤ amaProfit (fun _ => 0) tb (fun _ => 1) lam (additiveVal (V i))) := by sorry

end SampleMechDesign.Supplement
