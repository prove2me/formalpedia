-- Prove2me | Theorems.Thm_TwoSidedPI_lemma_4
-- name    : TwoSidedPI.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:05.6162+00:00
-- url     : https://prove2.me/theorems/adc319d6-41ce-4029-ad7d-2ce1b3e7a954
-- title:
--   Lemma 4 — Mechanism 1 is a $\frac13$-approximation of the optimal social welfare
-- statement:
--   Consider a matroid double auction: a finite set $B$ of unit-demand buyers, a finite set $S$ of unit-supply sellers (either may be empty), $|S|$ identical items, one per seller, and a matroid $\mathcal M_B=(B,\mathcal I_B)$ constraining which sets of buyers may be served. Each agent's value for an item is drawn independently from a known law $\mathcal D_a$ on $[0,\infty)$ with finite mean. Mechanism 1 is Algorithm 1 of the paper with prices $p_{i,j}(A_B,r)=\frac13\big(p_i(A_B,r)+p_j\big)$, ties in its arg max and arg min broken by fixed injective ranks.
--
--   **Lemma 4.** Mechanism 1 is a $\frac13$-approximation of the optimal social welfare:
--   $$
--   \mathbf E_{\mathbf v}\big[\mathbf v(A(\mathbf v))\big]\ \ge\ \frac13\,\mathbf E_{\mathbf v}\Big[\max_{X^*}\mathbf v(X^*)\Big],
--   $$
--   where $\mathbf v\sim\mathcal D$, $A(\mathbf v)=A_B(\mathbf v)\cup A_S(\mathbf v)\cup M_{\mathrm{SELL}}(\mathbf v)$ is the set of agents holding an item after the run on $\mathbf v$, and $\max_{X^*}\mathbf v(X^*)$ is the optimal social welfare over all feasible allocations.
--
--   This is the welfare half of Theorem 1.
--
--   Differences from the source:
--   - generalization: valuations non-negative and bounded (p.7), each $\mathcal D_a$ a distribution of such values → each $\mathcal D_a$ a probability law on $[0,\infty)$ with finite mean; reason: every bounded nonnegative law satisfies the hypothesis, and the prices $p_j=\mathbf E[\tilde v_j]$ and $p_i(A_B,r)$ only need finite means
--   - encoding: break ties arbitrarily, but always in the same way (footnote 6, p.9) → ties in the buyer arg max and the seller arg min broken by arbitrary injective ranks $\mathrm{rk}_B$, $\mathrm{rk}_S$, quantified over; reason: a fixed tie-breaking rule on finite sets is a strict total order, i.e. an injective rank
--   - encoding: disjoint finite sets of buyers $B$ and sellers $S$, a matroid $\mathcal M_B=(B,\mathcal I_B)$, independent values → agents `B ⊕ S` with `Fintype`, `M : Matroid B` with `M.E = univ`, profile law `Measure.pi D`; reason: Lean convention; same instances
--   - encoding: Algorithm 1's while loop with $\infty$ thresholds → `step` iterated $|B|+|S|$ times; thresholds and prices in `WithTop ℝ` with $\infty=\top$; reason: each live iteration removes a buyer or a seller and a finished state is a fixed point, so the iteration reaches the loop's exit; same run
--   - encoding: $\mathbf E_v[\max_{X^*} v(X^*)]$ (p.7) → the integral of `opt`, the maximum of $\sum_{i\in B'}v_i+\sum_{j\in K}v_j$ over $B'\in\mathcal I_B$, $K\subseteq S$, $|B'|+|K|\le|S|$; reason: these pairs are exactly the agent sets served by feasible allocations of the $|S|$ identical items
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, Lemma 4, p.28

import Mathlib
import Definitions.Def_TwoSidedPI_OptB
import Definitions.Def_TwoSidedPI_Prices
import Definitions.Def_TwoSidedPI_Outcome
import Definitions.Def_TwoSidedPI_Algorithm1

open MeasureTheory

namespace TwoSidedPI

/-- Lemma 4 (Braun, Kesselheim, arXiv:2105.15032v1, p.28): Mechanism 1 for matroid double
auctions is a `1/3`-approximation of the optimal social welfare:
`E_v[v(A(v))] ≥ (1/3) · E_v[max_{X*} v(X*)]`.

**Formalization Note** Agents are `B ⊕ S` (finite, possibly empty) with independent values (product law
`Measure.pi D`), each `𝒟_a` a probability law on `[0, ∞)` with finite mean; the matroid `M_B` is
on all of `B`; the arg max / arg min of Algorithm 1 break ties by the injective ranks `rkB`,
`rkS`. The benchmark is `opt`, the maximum welfare over all feasible
allocations (p.7). -/
theorem lemma_4 {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (hE : M.E = Set.univ)
    (D : B ⊕ S → Measure ℝ) [∀ a, IsProbabilityMeasure (D a)]
    (hD0 : ∀ a, D a (Set.Iio 0) = 0) (hDi : ∀ a, Integrable id (D a))
    (rkB : B → ℕ) (hrkB : Function.Injective rkB) (rkS : S → ℕ) (hrkS : Function.Injective rkS) :
    (1 / 3 : ℝ) * ∫ v, opt M v ∂(Measure.pi D) ≤ ∫ v, welfare1 M D rkB rkS v ∂(Measure.pi D) := by sorry

end TwoSidedPI
