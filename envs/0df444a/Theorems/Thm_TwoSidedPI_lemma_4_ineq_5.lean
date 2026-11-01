-- Prove2me | Theorems.Thm_TwoSidedPI_lemma_4_ineq_5
-- name    : TwoSidedPI.lemma_4_ineq_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:12.67498+00:00
-- url     : https://prove2.me/theorems/6e605c8a-0acc-4006-87c5-7bb505393125
-- title:
--   Proof of Lemma 4, inequality (5) — the buyers' surplus
-- statement:
--   Consider a matroid double auction: a finite set $B$ of unit-demand buyers, a finite set $S$ of unit-supply sellers (either may be empty), $|S|$ identical items, one per seller, and a matroid $\mathcal M_B=(B,\mathcal I_B)$ constraining which sets of buyers may be served. Each agent's value for an item is drawn independently from a known law $\mathcal D_a$ on $[0,\infty)$ with finite mean. Mechanism 1 is Algorithm 1 of the paper with prices $p_{i,j}(A_B,r)=\frac13\big(p_i(A_B,r)+p_j\big)$, ties in its arg max and arg min broken by fixed injective ranks. Write $A_B(\mathbf v)$, $A_S(\mathbf v)$, $r(\mathbf v)$, $M_{\mathrm{SELL}}(\mathbf v)$ for the final state of Mechanism 1 run on the truthful profile $\mathbf v\sim\mathcal D$, and let $\tilde{\mathbf v}$, $\mathbf v'$ be independent copies of $\mathbf v$ (ghost samples).
--
--   Let $P_i$ be the price at which buyer $i$ was asked to buy in the run on $\mathbf v$ (a seller had agreed to sell to her at that price), and $P_i=\infty$ if she was never asked, so that $(v_i-P_i)^+=0$. Then
--   $$
--   \sum_{i\in B}\mathbf E_{\mathbf v}\big[(v_i-P_i)^+\big]\ \ge\ \frac23\mathbf E_{\mathbf v,\mathbf v'}\big[\mathbf v'(\mathrm{OPT}_B(\mathbf v'\mid A_B(\mathbf v),r(\mathbf v)))\big]-\frac13\mathbf E_{\mathbf v,\tilde{\mathbf v}}\Big[\sum_{j\in M_{\mathrm{SELL}}(\mathbf v)}\tilde v_j\Big].
--   $$
--
--   This bounds the buyers' part of the surplus in the proof of Lemma 4.
--
--   Differences from the source:
--   - generalization: valuations non-negative and bounded (p.7), each $\mathcal D_a$ a distribution of such values → each $\mathcal D_a$ a probability law on $[0,\infty)$ with finite mean; reason: every bounded nonnegative law satisfies the hypothesis, and the prices $p_j=\mathbf E[\tilde v_j]$ and $p_i(A_B,r)$ only need finite means
--   - encoding: break ties arbitrarily, but always in the same way (footnote 6, p.9) → ties in the buyer arg max and the seller arg min broken by arbitrary injective ranks $\mathrm{rk}_B$, $\mathrm{rk}_S$, quantified over; reason: a fixed tie-breaking rule on finite sets is a strict total order, i.e. an injective rank
--   - encoding: disjoint finite sets of buyers $B$ and sellers $S$, a matroid $\mathcal M_B=(B,\mathcal I_B)$, independent values → agents `B ⊕ S` with `Fintype`, `M : Matroid B` with `M.E = univ`, profile law `Measure.pi D`; reason: Lean convention; same instances
--   - encoding: Algorithm 1's while loop with $\infty$ thresholds → `step` iterated $|B|+|S|$ times; thresholds and prices in `WithTop ℝ` with $\infty=\top$; reason: each live iteration removes a buyer or a seller and a finished state is a fixed point, so the iteration reaches the loop's exit; same run
--   - encoding: ghost samples $\tilde{\mathbf v}$ and $\mathbf v'$, independent copies of $\mathbf v$ → one copy `w.2` under `(Measure.pi D).prod (Measure.pi D)`; reason: each expectation involves only one ghost sample, and both have the law of $\mathbf v$; same values
--   - reading: $P_i=\infty$ for a buyer not offered a trade because she became infeasible, otherwise the price offered to $i$ (p.32) → $P_i=\infty$ for every buyer never asked to buy (also one never reached because $M_{\mathrm{SELL}}$ ran empty, or only paired with sellers who kept); reason: the page asserts that every other buyer is offered a trade, and its bound for a never-asked buyer is the minimum over an empty seller set, $\infty$; surplus $0$
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, proof of Lemma 4, inequality (5), p.33

import Mathlib
import Definitions.Def_TwoSidedPI_OptB
import Definitions.Def_TwoSidedPI_Prices
import Definitions.Def_TwoSidedPI_Outcome
import Definitions.Def_TwoSidedPI_Algorithm1

open MeasureTheory

namespace TwoSidedPI

/-- Inequality (5) in the proof of Lemma 4 (Braun, Kesselheim, arXiv:2105.15032v1, p.33), the
buyers' surplus bound:
`∑_{i ∈ B} E_v[(v_i − P_i)^+] ≥ (2/3) E_{v,v'}[v'(OPT_B(v'|A_B(v), r(v)))]
− (1/3) E_{v,ṽ}[∑_{j ∈ M_SELL(v)} ṽ_j]`, where `P_i` is the price at which buyer `i` was asked to
buy (`∞`, surplus `0`, if she never was) and `A_B(v)`, `r(v)`, `M_SELL(v)` are the final state
of Mechanism 1 on `v`.

**Formalization Note** Agents are `B ⊕ S` (finite, possibly empty) with independent values (product law
`Measure.pi D`), each `𝒟_a` a probability law on `[0, ∞)` with finite mean; the matroid `M_B` is
on all of `B`; the arg max / arg min of Algorithm 1 break ties by the injective ranks `rkB`,
`rkS`. The ghost samples `v'` and `ṽ` are independent copies of `v`
with the same law, so a single copy `w.2` under `(Measure.pi D).prod (Measure.pi D)` stands for
either. `(x − ∞)^+ = 0` (`surplus`). -/
theorem lemma_4_ineq_5 {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (hE : M.E = Set.univ)
    (D : B ⊕ S → Measure ℝ) [∀ a, IsProbabilityMeasure (D a)]
    (hD0 : ∀ a, D a (Set.Iio 0) = 0) (hDi : ∀ a, Integrable id (D a))
    (rkB : B → ℕ) (hrkB : Function.Injective rkB) (rkS : S → ℕ) (hrkS : Function.Injective rkS) :
    ∑ i : B, ∫ v, surplus (v (Sum.inl i)) (PB M D rkB rkS v i) ∂(Measure.pi D) ≥
      (2 / 3 : ℝ) * ∫ w, optB M (fun k => w.2 (Sum.inl k)) (run1 M D rkB rkS w.1).AB
          (run1 M D rkB rkS w.1).r ∂((Measure.pi D).prod (Measure.pi D))
      - (1 / 3 : ℝ) * ∫ w, ∑ j ∈ (run1 M D rkB rkS w.1).MSELL, w.2 (Sum.inr j)
          ∂((Measure.pi D).prod (Measure.pi D)) := by sorry

end TwoSidedPI
