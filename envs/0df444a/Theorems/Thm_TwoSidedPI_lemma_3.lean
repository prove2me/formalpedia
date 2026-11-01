-- Prove2me | Theorems.Thm_TwoSidedPI_lemma_3
-- name    : TwoSidedPI.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:01.852033+00:00
-- url     : https://prove2.me/theorems/2fee8210-db49-4372-8f9e-8b84191d7a89
-- title:
--   Lemma 3 — Mechanism 1 is DSBB, DSIC and IR
-- statement:
--   Consider a matroid double auction: a finite set $B$ of unit-demand buyers, a finite set $S$ of unit-supply sellers (either may be empty), $|S|$ identical items, one per seller, and a matroid $\mathcal M_B=(B,\mathcal I_B)$ constraining which sets of buyers may be served. Each agent's value for an item is drawn independently from a known law $\mathcal D_a$ on $[0,\infty)$ with finite mean. Mechanism 1 is Algorithm 1 of the paper with prices $p_{i,j}(A_B,r)=\frac13\big(p_i(A_B,r)+p_j\big)$, ties in its arg max and arg min broken by fixed injective ranks.
--
--   **Lemma 3.** Mechanism 1 is direct-trade strongly budget-balanced (DSBB): its outcome on every report profile is a composition of bilateral trades in which a buyer pays exactly what the seller of the same trade receives. Further, it is dominant-strategy incentive compatible (DSIC) and individually rational (IR) for all buyers and sellers.
--
--   These are the first three properties of Theorem 1.
--
--   Differences from the source:
--   - generalization: valuations non-negative and bounded (p.7), each $\mathcal D_a$ a distribution of such values → each $\mathcal D_a$ a probability law on $[0,\infty)$ with finite mean; reason: every bounded nonnegative law satisfies the hypothesis, and the prices $p_j=\mathbf E[\tilde v_j]$ and $p_i(A_B,r)$ only need finite means
--   - encoding: break ties arbitrarily, but always in the same way (footnote 6, p.9) → ties in the buyer arg max and the seller arg min broken by arbitrary injective ranks $\mathrm{rk}_B$, $\mathrm{rk}_S$, quantified over; reason: a fixed tie-breaking rule on finite sets is a strict total order, i.e. an injective rank
--   - encoding: disjoint finite sets of buyers $B$ and sellers $S$, a matroid $\mathcal M_B=(B,\mathcal I_B)$, independent values → agents `B ⊕ S` with `Fintype`, `M : Matroid B` with `M.E = univ`, profile law `Measure.pi D`; reason: Lean convention; same instances
--   - encoding: Algorithm 1's while loop with $\infty$ thresholds → `step` iterated $|B|+|S|$ times; thresholds and prices in `WithTop ℝ` with $\infty=\top$; reason: each live iteration removes a buyer or a seller and a finished state is a fixed point, so the iteration reaches the loop's exit; same run
--   - encoding: reports range over the valuation space $V_i$; payments signed (negative for buyers) → reports in $[0,\infty)$; outcome with served buyers, keeping sellers, buyer payments `pay` and seller receipts `recv`; reason: a unit-demand/unit-supply valuation is one nonnegative number; same outcomes
--   - encoding: DSBB: the outcome is a composition of bilateral trades with equal payments, each item traded at most once → `IsDSBB`: a finite set of triples $(i,j,p)$ with distinct buyers and distinct sellers that determines who is served, who keeps, and all payments; reason: with unit demand and unit supply a composition of bilateral trades is exactly such a set
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, Lemma 3, p.28

import Mathlib
import Definitions.Def_TwoSidedPI_OptB
import Definitions.Def_TwoSidedPI_Prices
import Definitions.Def_TwoSidedPI_Outcome
import Definitions.Def_TwoSidedPI_Algorithm1

open MeasureTheory

namespace TwoSidedPI

/-- Lemma 3 (Braun, Kesselheim, arXiv:2105.15032v1, p.28): Mechanism 1 for matroid double
auctions satisfies DSBB. Further, it is DSIC and IR for all buyers and sellers.

**Formalization Note** Agents are `B ⊕ S` (finite, possibly empty) with independent values (product law
`Measure.pi D`), each `𝒟_a` a probability law on `[0, ∞)` with finite mean; the matroid `M_B` is
on all of `B`; the arg max / arg min of Algorithm 1 break ties by the injective ranks `rkB`,
`rkS`. Reports range over `[0, ∞)`. -/
theorem lemma_3 {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (hE : M.E = Set.univ)
    (D : B ⊕ S → Measure ℝ) [∀ a, IsProbabilityMeasure (D a)]
    (hD0 : ∀ a, D a (Set.Iio 0) = 0) (hDi : ∀ a, Integrable id (D a))
    (rkB : B → ℕ) (hrkB : Function.Injective rkB) (rkS : S → ℕ) (hrkS : Function.Injective rkS) :
    IsDSBB (mech1 M D rkB rkS) ∧ IsDSIC (mech1 M D rkB rkS) ∧ IsIR (mech1 M D rkB rkS) := by sorry

end TwoSidedPI
