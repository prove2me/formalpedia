-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_density_restoring_partition
-- name    : RandomStreamCI.CodeIntersection.density_restoring_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:34.021102+00:00
-- url     : https://prove2.me/theorems/173afda7-6c7c-4473-b153-9f8d6bbff14a
-- title:
--   Lemma 11 — Fixed and dense ordered partition with tail entropy
-- statement:
--   Let $X$ have any probability law on Boolean assignments to a finite coordinate set $J$, and let $0<\gamma\le1$. Its positive support admits a finite ordered partition into nonempty parts $X^{(j)}$, each with fixed coordinates $I_j$ and assignment $\alpha_j$. In part $j$, the $I_j$ marginal is fixed to $\alpha_j$, and the complementary marginal is $\gamma$-dense on every subset of its coordinates. In addition,
--
--   $$H_\infty(X_{J\setminus I_j}\mid X\in X^{(j)})\ge H_\infty(X)-\gamma|I_j|+\log_2\Pr[X\in\bigcup_{i\ge j}X^{(i)}].$$
--
--   The endpoint $\gamma=1$ is included. This gives the complete fixed/dense decomposition with the ordered tail's nonpositive logarithm, not just existence of dense parts.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Lemma 11, printed p. 9 / PDF p. 9

import Definitions.Def_RandomStreamCI_CodeIntersection_Probability

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Lemma 11, p. 9 (18)–(19), including gamma = 1 and the signed ordered-tail logarithm. -/
theorem density_restoring_partition {J : Type} [Fintype J] [DecidableEq J]
    (p : PMF (J → Bool)) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ P : PartitionData J, IsRestoringPartition (weights p) γ P := by sorry

end RandomStreamCI.CodeIntersection
