-- Prove2me | Theorems.Thm_TwoSidedPI_lemma_6
-- name    : TwoSidedPI.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:17.908348+00:00
-- url     : https://prove2.me/theorems/ee26d114-5f39-46e9-9144-c2c6734331d9
-- title:
--   Lemma 6 (corrected: $i\notin X'$) — prices are non-decreasing for a fixed buyer–seller pair
-- statement:
--   Consider a matroid double auction: a finite set $B$ of unit-demand buyers, a finite set $S$ of unit-supply sellers (either may be empty), $|S|$ identical items, one per seller, and a matroid $\mathcal M_B=(B,\mathcal I_B)$ constraining which sets of buyers may be served. Each agent's value for an item is drawn independently from a known law $\mathcal D_a$ on $[0,\infty)$ with finite mean. Mechanism 1 is Algorithm 1 of the paper with prices $p_{i,j}(A_B,r)=\frac13\big(p_i(A_B,r)+p_j\big)$, ties in its arg max and arg min broken by fixed injective ranks.
--
--   **Lemma 6.** Fix buyer $i$ and seller $j$. For every $X\subseteq X'\subseteq B$ with $i\notin X'$ and every $r'\le r$,
--   $$
--   p_{i,j}(X,r)\ \le\ p_{i,j}(X',r'),
--   $$
--   where a price is $\infty$ when buyer $i$ cannot be feasibly added to the corresponding set with the corresponding number of items.
--
--   Since Mechanism 1 only adds buyers to $A_B$ and only decreases $r$, the price offered to a fixed pair can only go up as the process evolves.
--
--   Differences from the source:
--   - correction: every superset $X'\supseteq X$ → every superset $X'\supseteq X$ with $i\notin X'$; reason: the printed lemma fails for $i\in X'$: one buyer $i$, one seller $j$, $\mathcal D_i=\delta_1$, $\mathcal D_j=\delta_0$, $X=\emptyset$, $X'=\{i\}$, $r=r'=1$ gives $\frac13\le0$
--   - encoding: "for some set of remaining sellers $M_{\mathrm{SELL}}$" → no $M_{\mathrm{SELL}}$ parameter; reason: the price does not depend on $M_{\mathrm{SELL}}$
--   - generalization: valuations non-negative and bounded (p.7), each $\mathcal D_a$ a distribution of such values → each $\mathcal D_a$ a probability law on $[0,\infty)$ with finite mean; reason: every bounded nonnegative law satisfies the hypothesis, and the prices $p_j=\mathbf E[\tilde v_j]$ and $p_i(A_B,r)$ only need finite means
--   - encoding: disjoint finite sets of buyers $B$ and sellers $S$, a matroid $\mathcal M_B=(B,\mathcal I_B)$, independent values → agents `B ⊕ S` with `Fintype`, `M : Matroid B` with `M.E = univ`, profile law `Measure.pi D`; reason: Lean convention; same instances
--   - encoding: prices in $\mathbb R\cup\{\infty\}$ → prices in `WithTop ℝ`; reason: Lean convention; same values
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, Lemma 6, p.34

import Mathlib
import Definitions.Def_TwoSidedPI_OptB
import Definitions.Def_TwoSidedPI_Prices

open MeasureTheory

namespace TwoSidedPI

/-- Lemma 6 (Braun, Kesselheim, arXiv:2105.15032v1, p.34), corrected with `i ∉ X'`: fix buyer `i`
and seller `j`; then `p_{i,j}(X, r) ≤ p_{i,j}(X', r')` for every superset of allocated buyers
`X' ⊇ X` with `i ∉ X'` and every `r' ≤ r`, where `p_{i,j}(X, r) = ∞` when `i` cannot be feasibly
added to `X` with `r` items.

**Formalization Note** Prices are in `WithTop ℝ` (`⊤ = ∞`). The printed lemma omits `i ∉ X'`
and is false without it (one buyer `i`, one seller `j`, `𝒟_i = δ_1`, `𝒟_j = δ_0`, `X = ∅`,
`X' = {i}`, `r = r' = 1`: `1/3 ≤ 0`). The set `M_SELL` of the printed statement plays no role in
the price. Agents are `B ⊕ S` with independent values (product law), each `𝒟_a` a probability
law on `[0, ∞)` with finite mean; the matroid is on all of `B`. -/
theorem lemma_6 {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (hE : M.E = Set.univ)
    (D : B ⊕ S → Measure ℝ) [∀ a, IsProbabilityMeasure (D a)]
    (hD0 : ∀ a, D a (Set.Iio 0) = 0) (hDi : ∀ a, Integrable id (D a))
    (i : B) (j : S) (X X' : Finset B) (r r' : ℕ) (hXX' : X ⊆ X') (hr : r' ≤ r) (hi : i ∉ X') :
    price M D X r i j ≤ price M D X' r' i j := by sorry

end TwoSidedPI
