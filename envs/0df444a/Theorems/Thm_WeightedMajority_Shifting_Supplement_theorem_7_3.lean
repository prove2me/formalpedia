-- Prove2me | Theorems.Thm_WeightedMajority_Shifting_Supplement_theorem_7_3
-- name    : WeightedMajority.Shifting.Supplement.theorem_7_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:57:44.437878+00:00
-- url     : https://prove2.me/theorems/1f78b1d9-ce55-451f-9648-01ed4949c0c7
-- title:
--   Theorem 7.3 — the full effective mistake-budget implication chain
-- statement:
--   Let $(M_i)_{i\ge1}$ be a computable sequence of nonnegative integers. Define the following four statements.
--
--   1. (a) $\sum_i2^{-M_i}$ is finite and its real value is computable to arbitrary precision.
--   2. (b) There exists $c\in\mathbb R$ such that, for every effectively presented domain $X$ and every uniformly total-recursive binary pool $(\phi_i)$, there is an effective total online learner $A$ with $M_A(\mathcal S)\le M_i+c$ for every $i\ge1$ and every finite $\phi_i$-consistent sequence.
--   3. (c) For every such domain and pool there exist $c\in\mathbb R$, a positive cutoff $j$, and an effective total online learner $A$ with $M_A(\mathcal S)\le M_i+c$ for every $i\ge j$ and every finite $\phi_i$-consistent sequence.
--   4. (d) $\sum_i2^{-M_i}$ is finite.
--
--   Then all three implications hold:
--
--   $$(a)\Longrightarrow(b),\qquad(b)\Longrightarrow(c),\qquad(c)\Longrightarrow(d).$$
--
--   This separates effective summability, uniform attainable budgets, eventual budgets, and mere summability. In (b) the constant precedes the domain and pool; in (c) it follows them. Computability is part of the mathematical claim, for both the pool evaluator and the learner.
--
--   Differences from the source:
--   - encoding: positive member indices and positive inclusive cutoff j → natural indices shifted down by one, with an inclusive natural cutoff; reason: the correspondence i ↔ i+1 preserves every member and inequality
--   - encoding: domains supporting total recursive evaluation and algorithms → all primitive-codable domain presentations; Mathlib Computable on uncurried pool and learner maps; reason: this supplies an explicit effective presentation without limiting the domain or the horizon to be finite
--   - encoding: arbitrary-precision real sum → published IsComputableReal with recursive rational approximations and explicit Summable; reason: precision 2^(-r) is cofinal among positive error tolerances and the convergence premise prevents a default sum
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), DOI 10.1006/inco.1994.1009, p. 247, Theorem 7.3

import Definitions.Def_WeightedMajority_Shifting_Supplement_EffectiveBudgets

namespace WeightedMajority.Shifting.Supplement

theorem theorem_7_3 (M : ℕ → ℕ) (hM : Computable M) :
    (BudgetA M → BudgetB M) ∧ (BudgetB M → BudgetC M) ∧ (BudgetC M → BudgetD M) := by sorry

end WeightedMajority.Shifting.Supplement
