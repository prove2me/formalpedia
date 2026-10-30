-- Prove2me | Theorems.Thm_PandoraOrder_Tree_theorem_6
-- name    : PandoraOrder.Tree.theorem_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:01:51.627883+00:00
-- url     : https://prove2.me/theorems/d70b5812-fd7d-4a45-ad3c-a764e742e70f
-- title:
--   Theorem 6 — optimal search on a union of lines in polynomial time and space
-- statement:
--   For any finite union of disjoint nonempty lines partitioning the boxes, compute thresholds for each line independently and merge their heads with the fixed priority. The empty union when there are no boxes is permitted.
--
--   There are universal natural constants $C>0$ and $d$, independent of the number of boxes, all atom locations, all probabilities, costs and constraint data, such that the following holds for every source-model instance. Write $N=n+\sum_b s_b$ for the number of boxes plus the total atom-table size.
--
--   The specified concrete preprocessing program succeeds, returns exactly the semantic generalized thresholds and a legal linearization, and uses at most $C(N+1)^d$ primitive time and arena storage. Its search order is fixed before rewards are observed; each actual execution is a prefix. At every nonnegative incumbent $x$, its threshold policy $\pi_G$ is feasible and, for every admissible adaptive randomized competitor $\pi$,
--   $$\mathbb E[\operatorname{payoff}_x(\pi)]\le\mathbb E[\operatorname{payoff}_x(\pi_G)].$$
--   The benchmark includes arbitrary measurable independent private seeds with correlated choices across decisions, through the explicit behavioral-representation and integrability conclusion. Payoff keeps one maximum reward and subtracts every incurred cost. Search opens only below the threshold and stops at equality. For every nonnegative reward realization, the explicit costed implementation agrees with that rollout, and its total time and live arena storage, including preprocessing, obey the same polynomial bound.
--
--   This comparison is with all adaptive strategies, including those which switch between lines in response to observations. Nonempty component lists are the usual path encoding; omitting empty component lists changes no boxes or feasible search. There is no fixed bound on the number or length of lines.
--
--   Differences from the source:
--   - encoding: independent finite-support nonnegative box rewards and nonnegative costs → Fin-indexed boxes and atom tables with real masses, allowing repeated atoms and zero masses, and real nonnegative costs; reason: finite sums give the same product experiment; no rationality, common grid, positivity of costs, or normalization is imposed
--   - reading: page 7 conditions on reaching an incumbent, while Appendix C evaluates every nonnegative incumbent → restart the remaining suffix with its independent future laws and a specified incumbent; reason: this preserves the off-support incumbents required by equation (9) and exact threshold computation
--   - encoding: adaptive strategies with optional independent private randomness → full ordered-history behavioral kernels, with an explicit representation and integrability conclusion for measurable independently seeded strategies; reason: perfect recall and a finite horizon preserve arbitrary correlated seed choices; impossible histories may be completed with stopping
--   - reading: polynomial time and space in the number of boxes and finite support size → uniform polynomial bounds in n plus total support size for an explicit exact-real program, counting arithmetic, comparisons, accesses, control and arena storage; reason: the source measures support cardinality rather than bit length; weighted sums and affine roots are expanded into primitives, and total support size is polynomially equivalent
--   - reading: Theorem 1 says to open at equality but Algorithm 1 has a strict while test → open only when incumbent is strictly below the next threshold, stopping at equality; reason: Theorems 5 to 7 refer to the operational Generalized Pandora rule; equality events are retained
--   - encoding: ties resolved arbitrarily but consistently → prefer the smaller input label at equal thresholds and process child lists in increasing label order; reason: this fixes one permitted consistent priority before any reward is observed
--   - generalization: initial outside option zero in the search problem → optimality and execution bounds for every nonnegative initial incumbent; reason: setting the incumbent to zero gives the entire source claim; the source proofs already compare continuation states with a general incumbent
-- source:
--   Boodaghians et al., arXiv:2002.06968v2, Theorem 6, p. 9 (PDF p. 9); https://arxiv.org/abs/2002.06968v2

import Definitions.Def_PandoraOrder_Tree_Contracts

namespace PandoraOrder.Tree

theorem theorem_6 :
    ∃ C d : ℕ, 0 < C ∧ ∀ (n : ℕ) (I : Instance n) (Ls : List (List (Fin n))),
      LinesCover Ls → (∀ L ∈ Ls, L ≠ []) →
      AlgorithmContract I (unionConstraint Ls) (unionAvailable Ls)
        (unionProgram I Ls) (semanticUnion I Ls) (List.finRange n) C d := by sorry

end PandoraOrder.Tree
