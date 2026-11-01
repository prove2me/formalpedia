-- Prove2me | Theorems.Thm_TwoSidedPI_theorem_1
-- name    : TwoSidedPI.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:07.807716+00:00
-- url     : https://prove2.me/theorems/b5663743-c66d-4016-9d92-1080a9ca4773
-- title:
--   Theorem 1 — Mechanism 1 is DSBB, DSIC, IR and a $\frac13$-approximation for matroid double auctions
-- statement:
--   Consider a matroid double auction: a finite set $B$ of unit-demand buyers, a finite set $S$ of unit-supply sellers (either may be empty), $|S|$ identical items, one per seller, and a matroid $\mathcal M_B=(B,\mathcal I_B)$ constraining which sets of buyers may be served. Each agent's value for an item is drawn independently from a known law $\mathcal D_a$ on $[0,\infty)$ with finite mean. Mechanism 1 is Algorithm 1 of the paper with prices $p_{i,j}(A_B,r)=\frac13\big(p_i(A_B,r)+p_j\big)$, ties in its arg max and arg min broken by fixed injective ranks.
--
--   **Theorem 1.** Mechanism 1 is direct-trade strongly budget-balanced, dominant-strategy incentive compatible and individually rational for all buyers and sellers, and
--   $$
--   \mathbf E_{\mathbf v}\big[\mathbf v(A(\mathbf v))\big]\ \ge\ \frac13\,\mathbf E_{\mathbf v}\Big[\max_{X^*}\mathbf v(X^*)\Big],
--   $$
--   where $\mathbf v\sim\mathcal D=\times_a\mathcal D_a$ and $\max_{X^*}\mathbf v(X^*)$ is the optimal social welfare over all feasible allocations.
--
--   This is the paper's first main result: a strongly budget-balanced, truthful and individually rational mechanism with a constant welfare guarantee for two-sided markets with a matroid constraint on the buyers. It is the conjunction of Lemma 3 and Lemma 4.
--
--   Differences from the source:
--   - generalization: valuations non-negative and bounded (p.7), each $\mathcal D_a$ a distribution of such values → each $\mathcal D_a$ a probability law on $[0,\infty)$ with finite mean; reason: every bounded nonnegative law satisfies the hypothesis, and the prices $p_j=\mathbf E[\tilde v_j]$ and $p_i(A_B,r)$ only need finite means
--   - encoding: break ties arbitrarily, but always in the same way (footnote 6, p.9) → ties in the buyer arg max and the seller arg min broken by arbitrary injective ranks $\mathrm{rk}_B$, $\mathrm{rk}_S$, quantified over; reason: a fixed tie-breaking rule on finite sets is a strict total order, i.e. an injective rank
--   - encoding: disjoint finite sets of buyers $B$ and sellers $S$, a matroid $\mathcal M_B=(B,\mathcal I_B)$, independent values → agents `B ⊕ S` with `Fintype`, `M : Matroid B` with `M.E = univ`, profile law `Measure.pi D`; reason: Lean convention; same instances
--   - encoding: Algorithm 1's while loop with $\infty$ thresholds → `step` iterated $|B|+|S|$ times; thresholds and prices in `WithTop ℝ` with $\infty=\top$; reason: each live iteration removes a buyer or a seller and a finished state is a fixed point, so the iteration reaches the loop's exit; same run
--   - encoding: reports range over the valuation space $V_i$; payments signed (negative for buyers) → reports in $[0,\infty)$; outcome with served buyers, keeping sellers, buyer payments `pay` and seller receipts `recv`; reason: a unit-demand/unit-supply valuation is one nonnegative number; same outcomes
--   - encoding: DSBB: the outcome is a composition of bilateral trades with equal payments, each item traded at most once → `IsDSBB`: a finite set of triples $(i,j,p)$ with distinct buyers and distinct sellers that determines who is served, who keeps, and all payments; reason: with unit demand and unit supply a composition of bilateral trades is exactly such a set
--   - encoding: $\mathbf E_v[\max_{X^*} v(X^*)]$ (p.7) → the integral of `opt`, the maximum of $\sum_{i\in B'}v_i+\sum_{j\in K}v_j$ over $B'\in\mathcal I_B$, $K\subseteq S$, $|B'|+|K|\le|S|$; reason: these pairs are exactly the agent sets served by feasible allocations of the $|S|$ identical items
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, Theorem 1, p.10; proof in Appendix B (Lemmas 3 and 4, p.28)

import Mathlib
import Definitions.Def_TwoSidedPI_OptB
import Definitions.Def_TwoSidedPI_Prices
import Definitions.Def_TwoSidedPI_Outcome
import Definitions.Def_TwoSidedPI_Algorithm1

open MeasureTheory

namespace TwoSidedPI

/-- Theorem 1 (Braun, Kesselheim, arXiv:2105.15032v1, p.10): the mechanism for matroid double
auctions (Algorithm 1) is DSBB, DSIC and IR for all buyers and sellers and a `1/3`-approximation
to the optimal social welfare, `E_v[v(A(v))] ≥ (1/3) · E_v[max_{X*} v(X*)]`.

**Formalization Note** Agents are `B ⊕ S` (finite, possibly empty) with independent values (product law
`Measure.pi D`), each `𝒟_a` a probability law on `[0, ∞)` with finite mean; the matroid `M_B` is
on all of `B`; the arg max / arg min of Algorithm 1 break ties by the injective ranks `rkB`,
`rkS`. Reports range over `[0, ∞)`. The benchmark is `opt`, the
maximum welfare over all feasible allocations (p.7). -/
theorem theorem_1 {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (hE : M.E = Set.univ)
    (D : B ⊕ S → Measure ℝ) [∀ a, IsProbabilityMeasure (D a)]
    (hD0 : ∀ a, D a (Set.Iio 0) = 0) (hDi : ∀ a, Integrable id (D a))
    (rkB : B → ℕ) (hrkB : Function.Injective rkB) (rkS : S → ℕ) (hrkS : Function.Injective rkS) :
    IsDSBB (mech1 M D rkB rkS) ∧ IsDSIC (mech1 M D rkB rkS) ∧ IsIR (mech1 M D rkB rkS) ∧
      (1 / 3 : ℝ) * ∫ v, opt M v ∂(Measure.pi D) ≤
        ∫ v, welfare1 M D rkB rkS v ∂(Measure.pi D) := by sorry

end TwoSidedPI
