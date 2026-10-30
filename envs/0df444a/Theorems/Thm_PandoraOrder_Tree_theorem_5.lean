-- Prove2me | Theorems.Thm_PandoraOrder_Tree_theorem_5
-- name    : PandoraOrder.Tree.theorem_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:02:01.083783+00:00
-- url     : https://prove2.me/theorems/09d01252-215c-4ed7-9b3c-7e14dad24a3e
-- title:
--   Theorem 5 — optimal line search in polynomial time and space
-- statement:
--   For a single line, use the explicit backwards piecewise-affine line program. The empty line is permitted and only stopping is feasible.
--
--   There are universal natural constants $C>0$ and $d$, independent of the number of boxes, all atom locations, all probabilities, costs and constraint data, such that the following holds for every source-model instance. Write $N=n+\sum_b s_b$ for the number of boxes plus the total atom-table size.
--
--   The specified concrete preprocessing program succeeds, returns exactly the semantic generalized thresholds and a legal linearization, and uses at most $C(N+1)^d$ primitive time and arena storage. Its search order is fixed before rewards are observed; each actual execution is a prefix. At every nonnegative incumbent $x$, its threshold policy $\pi_G$ is feasible and, for every admissible adaptive randomized competitor $\pi$,
--   $$\mathbb E[\operatorname{payoff}_x(\pi)]\le\mathbb E[\operatorname{payoff}_x(\pi_G)].$$
--   The benchmark includes arbitrary measurable independent private seeds with correlated choices across decisions, through the explicit behavioral-representation and integrability conclusion. Payoff keeps one maximum reward and subtracts every incurred cost. Search opens only below the threshold and stops at equality. For every nonnegative reward realization, the explicit costed implementation agrees with that rollout, and its total time and live arena storage, including preprocessing, obey the same polynomial bound.
--
--   In addition, for every nonnegative incumbent the separately defined Bellman recursion equals the semantic optimal value over actual policies. This is exact optimality and exact root computation, including roots between atoms; no fixed support grid or bound on reward magnitudes is imposed.
--
--   Differences from the source:
--   - encoding: independent finite-support nonnegative box rewards and nonnegative costs → Fin-indexed boxes and atom tables with real masses, allowing repeated atoms and zero masses, and real nonnegative costs; reason: finite sums give the same product experiment; no rationality, common grid, positivity of costs, or normalization is imposed
--   - reading: page 7 conditions on reaching an incumbent, while Appendix C evaluates every nonnegative incumbent → restart the remaining suffix with its independent future laws and a specified incumbent; reason: this preserves the off-support incumbents required by equation (9) and exact threshold computation
--   - encoding: adaptive strategies with optional independent private randomness → full ordered-history behavioral kernels, with an explicit representation and integrability conclusion for measurable independently seeded strategies; reason: perfect recall and a finite horizon preserve arbitrary correlated seed choices; impossible histories may be completed with stopping
--   - reading: polynomial time and space in the number of boxes and finite support size → uniform polynomial bounds in n plus total support size for an explicit exact-real program, counting arithmetic, comparisons, accesses, control and arena storage; reason: the source measures support cardinality rather than bit length; weighted sums and affine roots are expanded into primitives, and total support size is polynomially equivalent
--   - reading: Theorem 1 says to open at equality but Algorithm 1 has a strict while test → open only when incumbent is strictly below the next threshold, stopping at equality; reason: Theorems 5 to 7 refer to the operational Generalized Pandora rule; equality events are retained
--   - encoding: ties resolved arbitrarily but consistently → prefer the smaller input label at equal thresholds and process child lists in increasing label order; reason: this fixes one permitted consistent priority before any reward is observed
--   - generalization: initial outside option zero in the search problem → optimality and execution bounds for every nonnegative initial incumbent; reason: setting the incumbent to zero gives the entire source claim; the source proofs already compare continuation states with a general incumbent
--   - generalization: a line consisting of all boxes → any duplicate-free list in a finite ambient instance, including the empty list; reason: taking the list to contain every box recovers the full theorem; unused boxes are inaccessible and an empty line permits only stopping
-- source:
--   Boodaghians et al., arXiv:2002.06968v2, Theorem 5, p. 8 (PDF p. 8); https://arxiv.org/abs/2002.06968v2

import Definitions.Def_PandoraOrder_Tree_Contracts

namespace PandoraOrder.Tree

theorem theorem_5 :
    ∃ C d : ℕ, 0 < C ∧ ∀ (n : ℕ) (I : Instance n) (L : List (Fin n)), L.Nodup →
      AlgorithmContract I (lineConstraint L) (lineAvailable L)
        (linePreprocess I L) (semanticLine I L) L C d ∧
      ∀ x : ℝ, 0 ≤ x → lineDP I L x = lineValue I L x := by sorry

end PandoraOrder.Tree
