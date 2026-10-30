-- Prove2me | Theorems.Thm_ShapleyScarf_CoreExistence_core_point_has_realizable_core_majorant
-- name    : ShapleyScarf.CoreExistence.core_point_has_realizable_core_majorant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:38:58.721801+00:00
-- url     : https://prove2.me/theorems/9ab0f5b2-f059-4c7e-ae6d-328370efeb12
-- title:
--   Section 5 — every payoff-core point has a realizable core majorant
-- statement:
--   Let $N$ be any finite nonempty set of traders and let $A=(a_{ij})$ be any real preference matrix, including ties. For a coalition $S$, let $V_A(S)$ contain exactly those payoff thresholds $x$ for which an $S$-permutation gives every member $i$ an item worth at least $x_i$. Let $C(V_A)$ be the payoff core defined using ambient interiors and all nonempty coalitions, including $N$.
--
--   For every $x\in C(V_A)$ there is a bijection $\sigma:N\to N$ whose actual payoff $u_\sigma(i)=a_{i,\sigma(i)}$ satisfies
--
--   $$x\le u_\sigma,\qquad u_\sigma\in C(V_A),\qquad \sigma\text{ is a core allocation}.$$
--
--   The inequality holds for every trader. Being a core allocation means that no nonempty coalition can permute its own goods so that every member strictly improves over $u_\sigma$. The allocation uses the original goods and their original utilities, without disposal, fractional goods or side payments.
--
--   This states the Section 5 observation for every payoff-core point, thereby retaining its actual-market conclusion rather than just a feasible upper bound. No preselected trading-cycle partition or core allocation is assumed.
--
--   **Formalization Note.** `marketGame` is the published characteristic function constructed from $A$, and `IsCoreAllocation` is the published strict-all-members blocking convention.
--
--   Differences from the source:
--   - reading: the core display starts with the free expression V(S) → the feasible term is V(N); reason: the immediately following sentence explicitly defines the core using V(N), including N among blocking coalitions
--   - encoding: a finite nonempty player set and its Euclidean payoff space → a type N with Fintype, DecidableEq and Nonempty, and the finite product N → ℝ; reason: finite indexing and decidable membership change no market or game instance; the product topology is the Euclidean topology
--   - encoding: a realizable permutation allocation and its actual payoff → a bijection σ : N → N and assignmentPayoff A σ, with IsCoreAllocation A σ; reason: bijections encode exactly the permutation matrices; the reused core predicate excludes strict improvement for every member of each nonempty coalition
-- source:
--   Shapley and Scarf, On cores and indivisibility, Journal of Mathematical Economics 1 (1974), published, DOI 10.1016/0304-4068(74)90033-0, https://doi.org/10.1016/0304-4068(74)90033-0; Section 5, paragraph after Figure 1, printed p. 113 / PDF p. 10; market core convention in Section 2, printed p. 107 / PDF p. 4.

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_MarketGame
import Definitions.Def_ShapleyScarf_TopTrading_Market
import Definitions.Def_ShapleyScarf_CoreExistence_payoffCore
import Definitions.Def_ShapleyScarf_CoreExistence_assignmentPayoff

namespace ShapleyScarf.CoreExistence

/-- Section 5, paragraph after Figure 1, printed p. 113 / PDF p. 10.
Every payoff-core point is majorized by the actual payoff of a core permutation allocation.
Majorization is coordinatewise and weak; a deviation in `IsCoreAllocation` requires strict
improvement for every member of a nonempty coalition. The payoff core uses the explicit
grand-coalition reading at printed p. 108 / PDF p. 5. -/
theorem core_point_has_realizable_core_majorant
    {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) (x : N → ℝ)
    (hx : x ∈ payoffCore (ShapleyScarf.Balanced.marketGame A)) :
    ∃ σ : N → N, Function.Bijective σ ∧
      (∀ i : N, x i ≤ assignmentPayoff A σ i) ∧
      assignmentPayoff A σ ∈ payoffCore (ShapleyScarf.Balanced.marketGame A) ∧
      ShapleyScarf.TopTrading.IsCoreAllocation A σ := by sorry

end ShapleyScarf.CoreExistence
