-- Prove2me | Theorems.Thm_PandoraOrder_Tree_theorem_7
-- name    : PandoraOrder.Tree.theorem_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:01:59.136481+00:00
-- url     : https://prove2.me/theorems/7ad119f6-b9fd-48ec-a0aa-2d44e81ddfbf
-- title:
--   Theorem 7 — optimal tree search in polynomial time and space
-- statement:
--   For every finite rooted tree on the boxes, apply the bottom-up tree program: merge completed child lists by accessible heads, compute the threshold of the parent prefixed to the merge, and retain all descendant thresholds.
--
--   There are universal natural constants $C>0$ and $d$, independent of the number of boxes, all atom locations, all probabilities, costs and constraint data, such that the following holds for every source-model instance. Write $N=n+\sum_b s_b$ for the number of boxes plus the total atom-table size.
--
--   The specified concrete preprocessing program succeeds, returns exactly the semantic generalized thresholds and a legal linearization, and uses at most $C(N+1)^d$ primitive time and arena storage. Its search order is fixed before rewards are observed; each actual execution is a prefix. At every nonnegative incumbent $x$, its threshold policy $\pi_G$ is feasible and, for every admissible adaptive randomized competitor $\pi$,
--   $$\mathbb E[\operatorname{payoff}_x(\pi)]\le\mathbb E[\operatorname{payoff}_x(\pi_G)].$$
--   The benchmark includes arbitrary measurable independent private seeds with correlated choices across decisions, through the explicit behavioral-representation and integrability conclusion. Payoff keeps one maximum reward and subtracts every incurred cost. Search opens only below the threshold and stops at equality. For every nonnegative reward realization, the explicit costed implementation agrees with that rollout, and its total time and live arena storage, including preprocessing, obey the same polynomial bound.
--
--   The root list contains every box exactly once and respects all parent-before-child constraints. Arbitrary tree depth and branching, singleton trees, deterministic rewards, zero costs and initial stopping are included. The assertion is the full exact tree-optimality theorem with both time and space, not an approximation or a conditional statement assuming the thresholds are optimal.
--
--   Differences from the source:
--   - encoding: independent finite-support nonnegative box rewards and nonnegative costs → Fin-indexed boxes and atom tables with real masses, allowing repeated atoms and zero masses, and real nonnegative costs; reason: finite sums give the same product experiment; no rationality, common grid, positivity of costs, or normalization is imposed
--   - reading: page 7 conditions on reaching an incumbent, while Appendix C evaluates every nonnegative incumbent → restart the remaining suffix with its independent future laws and a specified incumbent; reason: this preserves the off-support incumbents required by equation (9) and exact threshold computation
--   - encoding: adaptive strategies with optional independent private randomness → full ordered-history behavioral kernels, with an explicit representation and integrability conclusion for measurable independently seeded strategies; reason: perfect recall and a finite horizon preserve arbitrary correlated seed choices; impossible histories may be completed with stopping
--   - reading: polynomial time and space in the number of boxes and finite support size → uniform polynomial bounds in n plus total support size for an explicit exact-real program, counting arithmetic, comparisons, accesses, control and arena storage; reason: the source measures support cardinality rather than bit length; weighted sums and affine roots are expanded into primitives, and total support size is polynomially equivalent
--   - reading: Theorem 1 says to open at equality but Algorithm 1 has a strict while test → open only when incumbent is strictly below the next threshold, stopping at equality; reason: Theorems 5 to 7 refer to the operational Generalized Pandora rule; equality events are retained
--   - encoding: ties resolved arbitrarily but consistently → prefer the smaller input label at equal thresholds and process child lists in increasing label order; reason: this fixes one permitted consistent priority before any reward is observed
--   - reading: Algorithm 2 assigns L_l := [b_j] + L after processing b_l → prefix b_l, the vertex just processed; reason: j is undefined for a leaf and otherwise duplicates a child; the preceding threshold call and parent-first construction determine the intended index
--   - encoding: bottom-up queue in Algorithm 2 → repeatedly scan for the smallest ready vertex, merge its completed children, and compute its threshold; reason: this is a concrete deterministic topological schedule of the same bottom-up construction, and the scan cost is counted
--   - generalization: initial outside option zero in the search problem → optimality and execution bounds for every nonnegative initial incumbent; reason: setting the incumbent to zero gives the entire source claim; the source proofs already compare continuation states with a general incumbent
-- source:
--   Boodaghians et al., arXiv:2002.06968v2, Theorem 7, p. 11 (PDF p. 11); https://arxiv.org/abs/2002.06968v2

import Definitions.Def_PandoraOrder_Tree_Contracts

namespace PandoraOrder.Tree

theorem theorem_7 :
    ∃ C d : ℕ, 0 < C ∧ ∀ (n : ℕ) (I : Instance n)
      (T : HarelTarjan.Compressed.RootedTree (Fin n)),
      AlgorithmContract I (treeConstraint T) (treeAvailable T)
        (treeProgram I T) (semanticSubtree I T n T.root) (List.finRange n) C d := by sorry

end PandoraOrder.Tree
