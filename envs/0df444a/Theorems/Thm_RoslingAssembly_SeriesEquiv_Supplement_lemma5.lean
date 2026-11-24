-- Prove2me | Theorems.Thm_RoslingAssembly_SeriesEquiv_Supplement_lemma5
-- name    : RoslingAssembly.SeriesEquiv.Supplement.lemma5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:20:47.053877+00:00
-- url     : https://prove2.me/theorems/a9065b1c-c6ce-40ce-9569-3df7504e396a
-- title:
--   Lemma 5 — simultaneous eventual sibling balance and equality
-- statement:
--   Fix an item $i$ with $h_i\le0$ and strictly positive echelon holding costs on every $k\in P(i)$, under GA and the standing model assumptions. Let $n$ be any shortest-lead immediate predecessor of $i$. There exists one feasible optimal policy such that, for almost every demand path, a finite time is reached after which all of the following hold in every period:
--   $$
--   X^{M-\mu}_{kt}\le X^{M-\mu}_{qt}
--   \quad(k,q\in P(i),\ k<q,\ 0\le\mu\le M_k),
--   $$
--   $$
--   X^{M-\mu}_{it}=X^{M-\mu}_{nt}
--   \quad(0\le\mu\le M_i),\qquad Y^*_{it}=X^l_{nt}.
--   $$
--   All endpoints are included, and $X^{M-\mu}_{kt}$ is the position at age $M_k-\mu$ of item $k$. Optimality covers both $0<\alpha<1$ and $\alpha=1$ with the source criterion.
--
--   The simultaneous inequalities and equalities justify aggregation into a shortest-lead predecessor. The same policy and the same finite path-dependent transient serve every displayed clause.
--
--   **Formalization Note** No bounded-demand, initial-balance, finite-optimum or optimal-policy-existence hypothesis is added.
--
--   Differences from the source:
--   - encoding: the physical assembly model of §§1–2 → the published Model, Policy, Dynamics and Cost, with H1 = sum h, nonnegative backlogging cost, a probability demand law and a well-formed initial pipeline; reason: these are the physical coefficient and feasible-history conventions; no initial long-run balance is imposed
--   - reading: optimality at alpha = 1 means the normalized limit of (2), including (4) → HasAverageCost asserts the actual extended-valued limit; optimality compares feasible policies whose source criterion is defined; reason: neither a nonexistent limit nor infinity minus infinity has a source value; existence of the optimizer and its criterion remains a conclusion
--   - encoding: periods t = 1, 2, ... and inventory ages → decisions use k = t - 1 observed demands, with item-specific ages M_k - mu; reason: this is the published finite-history and forward-time convention
--   - reading: eventually, with the positive-mean-demand argument on pp. 572–573 → one policy and one almost-sure finite path-dependent transient for every later period and every clause; reason: positive iid mean makes accumulated demand exceed every finite bound almost surely; no deterministic bound is printed
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4):565–579, 1989, DOI 10.1287/opre.37.4.565, p. 572 (PDF 9), Lemma 5

import Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Criterion

namespace RoslingAssembly.SeriesEquiv.Supplement
open MeasureTheory

theorem lemma5 (S : Model) [IsProbabilityMeasure S.ν] (x0 : InitialPositions)
    (hStanding : Standing S x0) (hGA : GeneralizedAssumption S)
    (i n : ℕ) (hi : i ∈ Finset.Icc 1 S.N) (hhi : S.h i ≤ 0)
    (hPred : ∀ k ∈ S.predecessors i, 0 < S.h k)
    (hn : ShortestPredecessor S i n) :
    ∃ π : Policy, CriterionOptimal S x0 π ∧
      ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => S.ν),
        ∃ T : ℕ, ∀ t ≥ T, 1 ≤ t → LocalBalanceAt S x0 π ω i n t := by sorry

end RoslingAssembly.SeriesEquiv.Supplement
