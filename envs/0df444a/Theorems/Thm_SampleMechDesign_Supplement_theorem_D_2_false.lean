-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_theorem_D_2_false
-- name    : SampleMechDesign.Supplement.theorem_D_2_false
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:55:05.117636+00:00
-- url     : https://prove2.me/theorems/01177ecc-6e21-57fb-9f4d-ed1ada30f72b
-- title:
--   Theorem D.2 (corrected: refuted as printed) — the $\mathcal Q$-boosted AMA bound fails: one buyer, one item, maximum profit $U=0$
-- statement:
--   Theorem D.2 states: let $\mathcal M$ be the class of AMAs and let $w$ map sets of allocations $\mathcal Q$ to $[0,1]$ with $\sum w(\mathcal Q)\le1$; with probability $1-\delta$ over $S\sim\mathcal D^N$, for any $M\in\mathcal M$,
--   $$
--   |\mathrm{profit}_S(M)-\mathrm{profit}_{\mathcal D}(M)|\ \le\ 360U\sqrt{\frac{nm(n+|\mathcal Q_M|)\log(4n)}{N}}+4U\sqrt{\frac2N\ln\frac{4}{\delta\cdot w(\mathcal Q_M)}},
--   $$
--   where $U$ is the maximum profit of any mechanism in $\mathcal M$ over the support of $\mathcal D$.
--
--   This item refutes it. There are a nonnegative cost function, a distribution $\mathcal D$ with a finite support of normalized, nonnegative, monotone valuations, a weight function with $\sum w\le1$, $\delta\in(0,1)$ and $N\ge1$, for one buyer and one item, such that for every tie-breaking rule the maximum profit $U$ of the AMAs over the support exists and
--   $$
--   \Pr_{S\sim\mathcal D^N}\Big[\exists M\in\mathcal M,\ w(\mathcal Q_M)>0:\ |\mathrm{profit}_S(M)-\mathrm{profit}_{\mathcal D}(M)|>\text{the printed bound}\Big]\ >\ \delta .
--   $$
--   A witness: the cost is $10$ for the allocation giving the item and $0$ otherwise, $\mathcal D$ is uniform on $v(\text{item})\in\{0,1\}$, $w(\varnothing)=1$, $\delta=1/2$, $N=1$. Every AMA has profit at most $0$ on the support, so $U=0$ and the bound is $0$, while the AMA with weight $20$ and no boost ($\mathcal Q_M=\varnothing$) has profits $0$ and $-9.5$, so every sample deviates by $4.75$.
--
--   The failure is the one corrected in the published goal (correction C2): AMA profits can be negative, so the maximum profit does not bound their range. Under the published goal's reading (profits of every mechanism in $[0,U]$ on the support) the theorem is vacuous instead, since for every valuation vector some AMA has negative profit.
--
--   Differences from the source:
--   - correction: with probability 1 − δ, every AMA M satisfies |profit_S(M) − profit_D(M)| ≤ 360U√(nm(n + |Q_M|) log(4n)/N) + 4U√((2/N) ln(4/(δ·w(Q_M)))) (U the maximum profit over the support) → the negation at n = m = 1: some nonnegative cost, finitely supported D of normalized monotone valuations, weight function, δ ∈ (0, 1) and N ≥ 1 make the bad event have probability > δ, with U the attained maximum profit; reason: false as printed: AMA profits can be negative while U = 0 (cost 10 on the allocated item, D uniform on values 0 and 1, AMA weight 20 with no boost, profits 0 and −9.5); under the [0, U] range reading of base correction C2 the hypothesis is never satisfied and the theorem is vacuous; no corrected bound is supported by the paper, which prints no proof
--   - reading: the tie-breaking rule is not specified → every tie-breaking rule; reason: the refutation holds for all of them
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem D.2, p.46 (PDF p.46); Definition A.10, p.28

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_amaProfit
import Definitions.Def_SampleMechDesign_Supplement_boostedAllocs

open MeasureTheory

namespace SampleMechDesign.Supplement

/-- **Theorem D.2 is false as printed.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.46:
"Let M be the class of AMAs and let w be a weight function that maps sets of allocations Q to
[0, 1] such that ∑ w(Q) ≤ 1. With probability 1 − δ over S ∼ D^N, for any M ∈ M,
|profit_S(M) − profit_D(M)| ≤ 360U √(nm(n + |Q_M|) log(4n)/N) + 4U √((2/N) ln(4/(δ·w(Q_M))))",
with `U` the maximum profit of any mechanism of the class over the support of `D`.

The statement below refutes it with one buyer and one item (`n = m = 1`): there are a nonnegative
cost function `c`, a distribution `D` with finite support `s` of normalized, nonnegative, monotone
valuations, a weight function `wt` with `∑ wt ≤ 1`, `δ ∈ (0, 1)` and `N ≥ 1` such that, for every
tie-breaking rule, the maximum profit `U` of the AMAs over `s` exists and the event "some AMA `M`
with `wt(Q_M) > 0` deviates by more than the printed bound" has probability greater than `δ`.

**Formalization Note.** The failure is the one of the published goal's correction C2: the class
of AMAs has profits below `0` (a payment `(λ(Q^{-1}) − λ(Q*))/w` can be negative, and the cost is
subtracted), so the maximum profit `U` does not bound the range. Witness: `c` is `10` on the
allocation giving the item and `0` otherwise; `D` is uniform on `v(item) = 0` and `v(item) = 1`;
every AMA then has profit `≤ 0` on `s`, so `U = 0` and the bound is `0`, while the AMA with
`w = 20`, `λ = 0` (`Q_M = ∅`) has profit `0` and `−9.5`; `wt(∅) = 1`, `δ = 1/2`, `N = 1`. Under
the published goal's reading (profits in `[0, U]` for every mechanism of the class on the support)
the theorem would be vacuous instead: for every valuation vector some AMA has negative profit. -/
theorem theorem_D_2_false :
    ∃ (c : Bundles 1 1 → ℝ) (D : ProbabilityMeasure (BVal 1 1)) (s : Finset (BVal 1 1))
      (wt : Finset (Alloc 1 1) → ℝ) (δ : ℝ) (N : ℕ),
      (∀ b, 0 ≤ c b) ∧ (D : Measure (BVal 1 1)) (↑s)ᶜ = 0 ∧
      (∀ v ∈ s, 0 < (D : Measure (BVal 1 1)) {v}) ∧
      (∀ v ∈ s, ∀ j, v j ∅ = 0 ∧ ∀ q q', q ⊆ q' → 0 ≤ v j q ∧ v j q ≤ v j q') ∧
      (∀ Q, 0 ≤ wt Q ∧ wt Q ≤ 1) ∧ ∑ Q, wt Q ≤ 1 ∧ 0 < δ ∧ δ < 1 ∧ 1 ≤ N ∧
      ∀ tb : BVal 1 1 → Finset (Alloc 1 1) → Alloc 1 1, IsChoice tb → ∃ U : ℝ,
        IsGreatest {x | ∃ (w : Fin 1 → ℝ) (lam : Alloc 1 1 → ℝ), IsAMAParam w lam ∧
          ∃ v ∈ s, x = amaProfit c tb w lam v} U ∧
        ENNReal.ofReal δ < Measure.pi (fun _ : Fin N => (D : Measure (BVal 1 1)))
          {S : Fin N → BVal 1 1 | ∃ (w : Fin 1 → ℝ) (lam : Alloc 1 1 → ℝ), IsAMAParam w lam ∧
            0 < wt (boostedAllocs lam) ∧
            360 * U * √((1 : ℝ) * 1 * (1 + (boostedAllocs lam).card) * Real.log (4 * 1) / N) +
                4 * U * √(2 / (N : ℝ) * Real.log (4 / (δ * wt (boostedAllocs lam)))) <
              |(1 / (N : ℝ)) * ∑ i, amaProfit c tb w lam (S i) -
                ∫ v, amaProfit c tb w lam v ∂(D : Measure (BVal 1 1))|} := by sorry

end SampleMechDesign.Supplement
