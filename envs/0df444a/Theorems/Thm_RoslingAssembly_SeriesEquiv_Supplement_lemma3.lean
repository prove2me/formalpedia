-- Prove2me | Theorems.Thm_RoslingAssembly_SeriesEquiv_Supplement_lemma3
-- name    : RoslingAssembly.SeriesEquiv.Supplement.lemma3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:20:14.476012+00:00
-- url     : https://prove2.me/theorems/20e03907-1108-401d-b780-327ac0f39c29
-- title:
--   Lemma 3 — maximum feasible production at nonpositive holding cost
-- statement:
--   Fix any item $i$ with $h_i\le0$ in an assembly system satisfying GA and the standing physical and demand assumptions, from an arbitrary well-formed initial pipeline. There exists a feasible optimal policy $\pi$ such that, almost surely, in every period $t\ge1$,
--   $$Y^*_{it}=\min_{k\in P(i)}X^l_{kt}.$$
--   Here $P(i)$ is the immediate-predecessor set and $X^l_{kt}$ is item $k$'s position at age $l_k$. Optimality uses discounted cost for $0<\alpha<1$ and the source limiting average cost for $\alpha=1$.
--
--   This is the maximum-feasible-production policy required to eliminate an item with nonpositive echelon holding cost. It asserts existence, including existence of its objective value, without an optimal-attainment premise.
--
--   **Formalization Note** No bounded-demand, initial-balance, finite-optimum or optimal-policy-existence hypothesis is added.
--
--   Differences from the source:
--   - encoding: the physical assembly model of §§1–2 → the published Model, Policy, Dynamics and Cost, with H1 = sum h, nonnegative backlogging cost, a probability demand law and a well-formed initial pipeline; reason: these are the physical coefficient and feasible-history conventions; no initial long-run balance is imposed
--   - reading: optimality at alpha = 1 means the normalized limit of (2), including (4) → HasAverageCost asserts the actual extended-valued limit; optimality compares feasible policies whose source criterion is defined; reason: neither a nonexistent limit nor infinity minus infinity has a source value; existence of the optimizer and its criterion remains a conclusion
--   - encoding: periods t = 1, 2, ... and inventory ages → decisions use k = t - 1 observed demands, with item-specific ages M_k - mu; reason: this is the published finite-history and forward-time convention
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4):565–579, 1989, DOI 10.1287/opre.37.4.565, p. 572 (PDF 9), Lemma 3

import Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Criterion

namespace RoslingAssembly.SeriesEquiv.Supplement
open MeasureTheory

theorem lemma3 (S : Model) [IsProbabilityMeasure S.ν] (x0 : InitialPositions)
    (hStanding : Standing S x0) (hGA : GeneralizedAssumption S)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 S.N) (hhi : S.h i ≤ 0) :
    ∃ π : Policy, CriterionOptimal S x0 π ∧
      ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => S.ν), ∀ t ≥ 1,
        (decision π ω i t : WithTop ℝ) = predecessorCap S x0 π ω i t := by sorry

end RoslingAssembly.SeriesEquiv.Supplement
