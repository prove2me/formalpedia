-- Prove2me | Theorems.Thm_TwoSidedPI_lemma_7
-- name    : TwoSidedPI.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:14.810593+00:00
-- url     : https://prove2.me/theorems/dd7f1a50-0780-4427-88a5-de127dcb07b1
-- title:
--   Lemma 7 (corrected: $i\notin A'_B$) — non-decreasing prices for buyers
-- statement:
--   Consider a matroid double auction: a finite set $B$ of unit-demand buyers, a finite set $S$ of unit-supply sellers (either may be empty), $|S|$ identical items, one per seller, and a matroid $\mathcal M_B=(B,\mathcal I_B)$ constraining which sets of buyers may be served. Each agent's value for an item is drawn independently from a known law $\mathcal D_a$ on $[0,\infty)$ with finite mean. Mechanism 1 is Algorithm 1 of the paper with prices $p_{i,j}(A_B,r)=\frac13\big(p_i(A_B,r)+p_j\big)$, ties in its arg max and arg min broken by fixed injective ranks.
--
--   **Lemma 7.** Fix a buyer $i$. For all $T'\subseteq T\subseteq S$, $A_B\subseteq A'_B\subseteq B$ with $i\notin A'_B$, and $r'\le r$,
--   $$
--   \min_{j\in T}p_{i,j}(A_B,r)\ \le\ \min_{j\in T'}p_{i,j}(A'_B,r'),
--   $$
--   where a minimum over the empty set is $\infty$.
--
--   Since Mechanism 1 offers buyer $i$ the cheapest available seller, this says the price offered to a fixed buyer is non-decreasing as the process evolves.
--
--   Differences from the source:
--   - correction: every $A'_B\supseteq A_B$ → every $A'_B\supseteq A_B$ with $i\notin A'_B$; reason: the printed lemma fails for $i\in A'_B$: the counterexample of Lemma 6 with $T=T'=\{j\}$, $A_B=\emptyset$, $A'_B=\{i\}$ gives $\frac13\le0$
--   - generalization: valuations non-negative and bounded (p.7), each $\mathcal D_a$ a distribution of such values → each $\mathcal D_a$ a probability law on $[0,\infty)$ with finite mean; reason: every bounded nonnegative law satisfies the hypothesis, and the prices $p_j=\mathbf E[\tilde v_j]$ and $p_i(A_B,r)$ only need finite means
--   - encoding: disjoint finite sets of buyers $B$ and sellers $S$, a matroid $\mathcal M_B=(B,\mathcal I_B)$, independent values → agents `B ⊕ S` with `Fintype`, `M : Matroid B` with `M.E = univ`, profile law `Measure.pi D`; reason: Lean convention; same instances
--   - encoding: minimum of prices in $\mathbb R\cup\{\infty\}$, $\infty$ over the empty set (p.32) → `Finset.inf` in `WithTop ℝ`; reason: Lean convention; same values
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, Lemma 7, p.35

import Mathlib
import Definitions.Def_TwoSidedPI_OptB
import Definitions.Def_TwoSidedPI_Prices

open MeasureTheory

namespace TwoSidedPI

/-- Lemma 7, non-decreasing prices for buyers (Braun, Kesselheim, arXiv:2105.15032v1, p.35),
corrected with `i ∉ A'_B`: fix a buyer `i`; then for any `T' ⊆ T ⊆ S`, `A'_B ⊇ A_B` with
`i ∉ A'_B`, and `r' ≤ r`, `min_{j ∈ T} p_{i,j}(A_B, r) ≤ min_{j ∈ T'} p_{i,j}(A'_B, r')`.

**Formalization Note** Prices are in `WithTop ℝ` (`⊤ = ∞`) and the minimum is `Finset.inf`, which
is `∞` over the empty set (p.32: "the minimum is taken over the empty set and we do not consider
buyer i anymore"). The printed lemma omits `i ∉ A'_B` and is false without it (the instance of
Lemma 6 with `T = T' = {j}`). Agents are `B ⊕ S` with independent values (product law), each
`𝒟_a` a probability law on `[0, ∞)` with finite mean; the matroid is on all of `B`. -/
theorem lemma_7 {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (hE : M.E = Set.univ)
    (D : B ⊕ S → Measure ℝ) [∀ a, IsProbabilityMeasure (D a)]
    (hD0 : ∀ a, D a (Set.Iio 0) = 0) (hDi : ∀ a, Integrable id (D a))
    (i : B) (T T' : Finset S) (hT : T' ⊆ T) (AB AB' : Finset B) (r r' : ℕ)
    (hAB : AB ⊆ AB') (hr : r' ≤ r) (hi : i ∉ AB') :
    T.inf (fun j => price M D AB r i j) ≤ T'.inf (fun j => price M D AB' r' i j) := by sorry

end TwoSidedPI
