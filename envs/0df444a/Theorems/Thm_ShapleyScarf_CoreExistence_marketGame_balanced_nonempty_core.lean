-- Prove2me | Theorems.Thm_ShapleyScarf_CoreExistence_marketGame_balanced_nonempty_core
-- name    : ShapleyScarf.CoreExistence.marketGame_balanced_nonempty_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:39:45.259147+00:00
-- url     : https://prove2.me/theorems/2c5c96ef-7bed-4bd3-99fa-e3afa8b263c4
-- title:
--   Section 4, Theorem — balancedness and a nonempty market core
-- statement:
--   Let $N$ be any finite nonempty set of traders, with item $j$ initially owned by trader $j$, and let $A=(a_{ij})$ be any real preference matrix. Equal values represent indifference, and negative values are permitted. A coalition can reshuffle only its own indivisible items. Its payoff set $V_A(S)$ consists of thresholds attainable or exceeded by an $S$-permutation.
--
--   The market game is balanced, its payoff core is nonempty, and an actual permutation allocation belongs to that core:
--
--   $$\begin{gathered}
--   V_A\text{ satisfies (a), (b), (c), and (e)},\qquad C(V_A)\ne\varnothing,\\
--   \exists\sigma:N\overset{\sim}{\longrightarrow}N,\quad u_\sigma\in C(V_A)\ \text{and}\ \sigma\text{ is a core allocation},\qquad u_\sigma(i)=a_{i,\sigma(i)}.
--   \end{gathered}$$
--
--   Conditions (a)–(c) are closedness, downward closure in coalition coordinates, and boundedness and nonemptiness of the individually rational coordinate slice. Condition (e) is $\bigcap_{S\in T}V_A(S)\subseteq V_A(N)$ for every family with nonnegative balancing weights covering each trader with total weight one. Here
--
--   $$C(V_A)=V_A(N)\setminus\bigcup_{\varnothing\ne S\subseteq N}\operatorname{int}_{\mathbb R^N}V_A(S).$$
--
--   A core allocation excludes every reshuffling by a nonempty coalition that makes all its members strictly better off. The goal contains both clauses of the Section 4 theorem and spells out the actual-market interpretation explained in Section 5. Balancedness, payoff-core existence and allocation existence are conclusions, without a TTC partition or an assumed core witness.
--
--   **Formalization Note.** The published market and balance definitions are used without alteration. All finite nonempty markets and all real matrices are quantified over; no convexification, utility normalization or strict-order assumption is imposed.
--
--   Differences from the source:
--   - reading: the core display starts with the free expression V(S) → the feasible term is V(N); reason: the immediately following sentence explicitly defines the core using V(N), including N among blocking coalitions
--   - encoding: a finite nonempty player set and its Euclidean payoff space → a type N with Fintype, DecidableEq and Nonempty, and the finite product N → ℝ; reason: finite indexing and decidable membership change no market or game instance; the product topology is the Euclidean topology
--   - encoding: a realizable permutation allocation and its actual payoff → a bijection σ : N → N and assignmentPayoff A σ, with IsCoreAllocation A σ; reason: bijections encode exactly the permutation matrices; the reused core predicate excludes strict improvement for every member of each nonempty coalition
-- source:
--   Shapley and Scarf, On cores and indivisibility, Journal of Mathematical Economics 1 (1974), published, DOI 10.1016/0304-4068(74)90033-0, https://doi.org/10.1016/0304-4068(74)90033-0; Section 4, Theorem, printed p. 110 / PDF p. 7; Section 2, core allocation, printed p. 107 / PDF p. 4; Section 5, realizability, printed p. 113 / PDF p. 10.

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_MarketGame
import Definitions.Def_ShapleyScarf_Balanced_BalancedGame
import Definitions.Def_ShapleyScarf_TopTrading_Market
import Definitions.Def_ShapleyScarf_CoreExistence_payoffCore
import Definitions.Def_ShapleyScarf_CoreExistence_assignmentPayoff

namespace ShapleyScarf.CoreExistence

/-- Section 4, Theorem, printed p. 110 / PDF p. 7, including its full core consequence.
The last conjunct spells out the actual-market interpretation of Sections 2 and 5
(printed pp. 107 and 113 / PDF pp. 4 and 10). The payoff core follows the grand-coalition
reading explicitly stated in the prose at printed p. 108 / PDF p. 5. -/
theorem marketGame_balanced_nonempty_core
    {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) :
    ShapleyScarf.Balanced.IsBalancedGame (ShapleyScarf.Balanced.marketGame A) ∧
      (payoffCore (ShapleyScarf.Balanced.marketGame A)).Nonempty ∧
      ∃ σ : N → N, Function.Bijective σ ∧
        assignmentPayoff A σ ∈ payoffCore (ShapleyScarf.Balanced.marketGame A) ∧
        ShapleyScarf.TopTrading.IsCoreAllocation A σ := by sorry

end ShapleyScarf.CoreExistence
