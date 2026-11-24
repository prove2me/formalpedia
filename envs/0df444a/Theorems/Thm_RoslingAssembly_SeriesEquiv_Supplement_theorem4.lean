-- Prove2me | Theorems.Thm_RoslingAssembly_SeriesEquiv_Supplement_theorem4
-- name    : RoslingAssembly.SeriesEquiv.Supplement.theorem4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:22:55.450431+00:00
-- url     : https://prove2.me/theorems/841c6704-a888-4f48-9bcb-b2322ba436e1
-- title:
--   Theorem 4 — practical necessity of the Generalized Assumption (corrected: (ii) is false as printed; the item states (i), (iii) and the negation of (ii))
-- statement:
--   Work in the assembly model of §§1–2 with $0<\alpha\le1$, iid nonnegative demand with a density and finite positive mean $\lambda$, a well-formed initial pipeline, and the source criterion (discounted cost for $\alpha<1$, the normalized limiting average cost for $\alpha=1$). For each item $i$ write
--   $$
--   g_i=h_i\alpha^{-M_{s(i)}}+\sum_{k\in B(i)}h_k\alpha^{-M_{s(k)}},
--   $$
--   where $B(i)$ is the set of all predecessors of $i$. Theorem 4 has three parts.
--
--   1. If $g_i<0$ for some $i$, the minimal cost of Problem P is unbounded below: for every real $C$ some feasible policy has a defined criterion value below $C$.
--   2. Part (ii) of the source claims: if $g_j\ge0$ for all items and $g_i=0$ for some $i$, there is an optimal policy for which $X^l_{it}$ is unbounded above for all $t\ge M_N-M_{s(i)}+1$. **This is false as printed** and the item states its negation. Counterexample: one item, $l_1=1$, $h_1=H_1=0$, $p=1$, $\alpha=1/2$, Exp(1) demand, zero initial stock. Then $g_1=0$, and the cost of any feasible policy is $\sum_t\alpha^{t}\,\mathbb E[(D-Y_{1t})^+]$ with $D\sim\Gamma(2,1)$, strictly positive. The constant order-up-to policies $Y_{1t}=S$ cost $(S+2)e^{-S}\to0$, so no feasible policy attains the infimum $0$ and no optimal policy exists.
--   3. If $g_j>0$ for all items but $\sum_{j=1}^N h_j\alpha^{-M_{s(j)}}<p+H_1$ fails, there is an optimal policy whose accumulated production of every item $i$, $\sum_{s\le t}(Y_{is}-X_{is})$, is bounded by $\max_k X_{k1}-X_{i1}$ for all $t$.
--
--   The theorem shows that the Generalized Assumption is practically necessary for a long-run analysis.
--
--   **Formalization Note** "Unbounded above" in (ii) is read as: for each such $t$ and each real $B$, $X^l_{it}>B$ with positive probability. The refutation does not depend on this reading, because the counterexample has no optimal policy at all. The bound in (iii) is written as "some $k$ with accumulated production $\le X_{k1}-X_{i1}$", which is equivalent to the bound by the maximum over the finite nonempty item set. Part (i) is also published, in a different model encoding, as theorem `1092141e-d094-4486-8bce-3710197088b1`; it is restated here so that the item covers the whole of Theorem 4.
--
--   Differences from the source:
--   - encoding: the physical assembly model of §§1–2 → the published Model, Policy, Dynamics and Cost, with H1 = sum h, nonnegative backlogging cost, a probability demand law and a well-formed initial pipeline; reason: these are the physical coefficient and feasible-history conventions
--   - reading: optimality and the minimal cost of Problem P, including alpha = 1 → CriterionOptimal and HasCriterion (defined signed expectation for alpha < 1, actual normalized limit of (2) with (4) at alpha = 1); reason: neither a nonexistent limit nor infinity minus infinity has a source value
--   - correction: part (ii), "there is an optimal policy for which X^l_it is unbounded above" → the negation of part (ii); reason: in Problem P, whose decisions are real numbers, the one-item example above satisfies every hypothesis of (ii) and has no optimal policy; the source's proof of (ii) is "As above, except that the final inequality is an equality" (p. 578), which shows that extra stock costs nothing but not that an optimum is attained
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4):565–579, 1989, DOI 10.1287/opre.37.4.565, p. 574 (PDF 11), Theorem 4; proof p. 578 (PDF 15)

import Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Criterion

namespace RoslingAssembly.SeriesEquiv.Supplement
open MeasureTheory

theorem theorem4 :
    (∀ (S : Model) [IsProbabilityMeasure S.ν] (x0 : InitialPositions),
      Standing S x0 →
      (∃ i ∈ Finset.Icc 1 S.N,
        weightedHolding S i + ∑ k ∈ allPredecessors S i, weightedHolding S k < 0) →
      ∀ C : ℝ, ∃ σ : Policy, S.Feasible x0 σ ∧
        ∃ d : EReal, HasCriterion S σ d ∧ d < (C : EReal)) ∧
    ¬ (∀ (S : Model) [IsProbabilityMeasure S.ν] (x0 : InitialPositions),
      Standing S x0 →
      (∀ j ∈ Finset.Icc 1 S.N,
        0 ≤ weightedHolding S j + ∑ k ∈ allPredecessors S j, weightedHolding S k) →
      ∀ i ∈ Finset.Icc 1 S.N,
        weightedHolding S i + ∑ k ∈ allPredecessors S i, weightedHolding S k = 0 →
        ∃ π : Policy, CriterionOptimal S x0 π ∧
          ∀ t ≥ S.M S.N - S.M (S.succ i) + 1, ∀ B : ℝ,
            0 < (Measure.infinitePi fun _ : ℕ => S.ν)
              {ω | B < S.pos x0 π ω i t (S.lead i)}) ∧
    (∀ (S : Model) [IsProbabilityMeasure S.ν] (x0 : InitialPositions),
      Standing S x0 →
      (∀ j ∈ Finset.Icc 1 S.N,
        0 < weightedHolding S j + ∑ k ∈ allPredecessors S j, weightedHolding S k) →
      ¬ (∑ j ∈ Finset.Icc 1 S.N, weightedHolding S j) < S.p + S.H1 →
      ∃ π : Policy, CriterionOptimal S x0 π ∧
        ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => S.ν),
          ∀ i ∈ Finset.Icc 1 S.N, ∀ t ≥ 1, ∃ k ∈ Finset.Icc 1 S.N,
            ∑ s ∈ Finset.Icc 1 t, (decision π ω i s - S.pos x0 π ω i s 1) ≤
              x0 k 1 - x0 i 1) := by sorry

end RoslingAssembly.SeriesEquiv.Supplement
