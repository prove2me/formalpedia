-- Prove2me | Theorems.Thm_TwoSidedPI_lemma_4_base_value
-- name    : TwoSidedPI.lemma_4_base_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:10.182855+00:00
-- url     : https://prove2.me/theorems/9ba389db-0054-4b17-8eea-159213db18ee
-- title:
--   Proof of Lemma 4, base value — the prices recover a third of the relaxed optimum
-- statement:
--   Consider a matroid double auction: a finite set $B$ of unit-demand buyers, a finite set $S$ of unit-supply sellers (either may be empty), $|S|$ identical items, one per seller, and a matroid $\mathcal M_B=(B,\mathcal I_B)$ constraining which sets of buyers may be served. Each agent's value for an item is drawn independently from a known law $\mathcal D_a$ on $[0,\infty)$ with finite mean. Mechanism 1 is Algorithm 1 of the paper with prices $p_{i,j}(A_B,r)=\frac13\big(p_i(A_B,r)+p_j\big)$, ties in its arg max and arg min broken by fixed injective ranks. Write $A_B(\mathbf v)$, $A_S(\mathbf v)$, $r(\mathbf v)$, $M_{\mathrm{SELL}}(\mathbf v)$ for the final state of Mechanism 1 run on the truthful profile $\mathbf v\sim\mathcal D$, and let $\tilde{\mathbf v}$, $\mathbf v'$ be independent copies of $\mathbf v$ (ghost samples).
--
--   For a buyer $i\in A_B(\mathbf v)$ let $P_i$ be the price she paid, and for a seller $j\in A_S(\mathbf v)$ let $P_j$ be the price she refused when keeping her item. Then
--   $$
--   \mathbf E_{\mathbf v}\Big[\sum_{i\in A_B(\mathbf v)\cup A_S(\mathbf v)}P_i\Big]\ \ge\ \frac13\mathbf E_{\mathbf v}\big[\mathbf v(\mathrm{OPT}_B(\mathbf v))\big]-\frac13\mathbf E_{\mathbf v,\tilde{\mathbf v}}\big[\tilde{\mathbf v}(\mathrm{OPT}_B(\tilde{\mathbf v}\mid A_B(\mathbf v),r(\mathbf v)))\big]+\frac13\mathbf E_{\mathbf v,\tilde{\mathbf v}}\Big[\sum_{j\in S\setminus M_{\mathrm{SELL}}(\mathbf v)}\tilde v_j\Big],
--   $$
--   where $\mathrm{OPT}_B(\mathbf v)=\mathrm{OPT}_B(\mathbf v\mid\emptyset,|S|)$.
--
--   This is the base-value half of the proof of Lemma 4: the part of the welfare below the prices the agents beat.
--
--   Differences from the source:
--   - generalization: valuations non-negative and bounded (p.7), each $\mathcal D_a$ a distribution of such values → each $\mathcal D_a$ a probability law on $[0,\infty)$ with finite mean; reason: every bounded nonnegative law satisfies the hypothesis, and the prices $p_j=\mathbf E[\tilde v_j]$ and $p_i(A_B,r)$ only need finite means
--   - encoding: break ties arbitrarily, but always in the same way (footnote 6, p.9) → ties in the buyer arg max and the seller arg min broken by arbitrary injective ranks $\mathrm{rk}_B$, $\mathrm{rk}_S$, quantified over; reason: a fixed tie-breaking rule on finite sets is a strict total order, i.e. an injective rank
--   - encoding: disjoint finite sets of buyers $B$ and sellers $S$, a matroid $\mathcal M_B=(B,\mathcal I_B)$, independent values → agents `B ⊕ S` with `Fintype`, `M : Matroid B` with `M.E = univ`, profile law `Measure.pi D`; reason: Lean convention; same instances
--   - encoding: Algorithm 1's while loop with $\infty$ thresholds → `step` iterated $|B|+|S|$ times; thresholds and prices in `WithTop ℝ` with $\infty=\top$; reason: each live iteration removes a buyer or a seller and a finished state is a fixed point, so the iteration reaches the loop's exit; same run
--   - encoding: ghost samples $\tilde{\mathbf v}$ and $\mathbf v'$, independent copies of $\mathbf v$ → one copy `w.2` under `(Measure.pi D).prod (Measure.pi D)`; reason: each expectation involves only one ghost sample, and both have the law of $\mathbf v$; same values
--   - encoding: $P_i$ for $i\in A_B(\mathbf v)\cup A_S(\mathbf v)$, the price the agent's value exceeded → the payment `pay i` of a buyer in $A_B(\mathbf v)$ and the last price offered `PS v j` to a seller in $A_S(\mathbf v)$; reason: a served buyer pays the price she accepted, and a seller who keeps is offered no further price; same values
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, proof of Lemma 4, base value, p.30

import Mathlib
import Definitions.Def_TwoSidedPI_OptB
import Definitions.Def_TwoSidedPI_Prices
import Definitions.Def_TwoSidedPI_Outcome
import Definitions.Def_TwoSidedPI_Algorithm1

open MeasureTheory

namespace TwoSidedPI

/-- The base-value bound in the proof of Lemma 4 (Braun, Kesselheim, arXiv:2105.15032v1, p.30):
`E_v[∑_{i ∈ A_B(v) ∪ A_S(v)} P_i] ≥ (1/3) E_v[v(OPT_B(v))] − (1/3) E_{v,ṽ}[ṽ(OPT_B(ṽ|A_B(v), r(v)))]
+ (1/3) E_{v,ṽ}[∑_{j ∈ S \ M_SELL(v)} ṽ_j]`, where `A_B(v)`, `A_S(v)`, `r(v)`, `M_SELL(v)` are
the final state of Mechanism 1 on `v`, `P_i` is the price paid by a buyer `i ∈ A_B(v)` or the
price refused by a seller `i ∈ A_S(v)` who kept her item, and `OPT_B(v) = OPT_B(v|∅, |S|)`.

**Formalization Note** Agents are `B ⊕ S` (finite, possibly empty) with independent values (product law
`Measure.pi D`), each `𝒟_a` a probability law on `[0, ∞)` with finite mean; the matroid `M_B` is
on all of `B`; the arg max / arg min of Algorithm 1 break ties by the injective ranks `rkB`,
`rkS`. The ghost sample `ṽ` is an independent copy of `v`:
`E_{v,ṽ}` integrates over `(Measure.pi D).prod (Measure.pi D)`. The price paid by `i ∈ A_B(v)`
is `(mech1 … v).pay i`; the price refused by `j ∈ A_S(v)` is the last price offered to her,
`PS … v j`. -/
theorem lemma_4_base_value {B S : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S]
    (M : Matroid B) (hE : M.E = Set.univ)
    (D : B ⊕ S → Measure ℝ) [∀ a, IsProbabilityMeasure (D a)]
    (hD0 : ∀ a, D a (Set.Iio 0) = 0) (hDi : ∀ a, Integrable id (D a))
    (rkB : B → ℕ) (hrkB : Function.Injective rkB) (rkS : S → ℕ) (hrkS : Function.Injective rkS) :
    ∫ v, (∑ i ∈ (run1 M D rkB rkS v).AB, (mech1 M D rkB rkS v).pay i +
        ∑ j ∈ (run1 M D rkB rkS v).AS, PS M D rkB rkS v j) ∂(Measure.pi D) ≥
      (1 / 3 : ℝ) * ∫ v, optB M (fun k => v (Sum.inl k)) ∅ (Fintype.card S) ∂(Measure.pi D)
      - (1 / 3 : ℝ) * ∫ w, optB M (fun k => w.2 (Sum.inl k)) (run1 M D rkB rkS w.1).AB
          (run1 M D rkB rkS w.1).r ∂((Measure.pi D).prod (Measure.pi D))
      + (1 / 3 : ℝ) * ∫ w, ∑ j ∈ Finset.univ \ (run1 M D rkB rkS w.1).MSELL, w.2 (Sum.inr j)
          ∂((Measure.pi D).prod (Measure.pi D)) := by sorry

end TwoSidedPI
