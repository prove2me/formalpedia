-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_Supplement_parity_approximation_lower
-- name    : StabilityDichotomies.Solvability.Supplement.parity_approximation_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:36:17.486143+00:00
-- url     : https://prove2.me/theorems/c1ac0a65-51fa-4e83-bf7c-52dbec7406c1
-- title:
--   Proposition 4.11 — Sparse linear lower bound for four-variable parity approximation
-- statement:
--   Consider the language Λ₄ consisting of the two four-variable parity relations. There exist constants ε₀ ∈ (0,1), c₀ > 0, an integer D₀ ≥ 1, and an unbounded set N₀ ⊆ ℕ such that the following holds for every randomized algorithm A that (1−ε₀)-approximates CSP(Λ₄) and every n ∈ N₀. There is a satisfiable instance I=(V,C) over Λ₄ with
--
--   $$|V|=n,\qquad |C|\le D_0 n,\qquad \operatorname{ASens}(A,I)\ge c_0 n.$$
--
--   All four witnesses are chosen before A and n. Approximation means an expected violation count of at most ε₀|C| on every satisfiable input; output laws can have arbitrary real probabilities. Sensitivity averages the optimal transport distance with unnormalized Hamming cost over deletion of one constraint occurrence.
--
--   This is the sparse source lower bound supporting the lower branch of Theorem 4.1. It is unconditional and does not assume the existence of codes or hard instances. The printed theorem's existential constants are retained. The source supplies positive witnesses on p.27 in terms of uniform locally testable code parameters; their existence is part of the proof obligation, not an extra hypothesis.
--
--   Differences from the source:
--   - encoding: a finite variable set V of cardinality n → the carrier Fin n; reason: finite carriers are represented by numbered variables with unrestricted scopes, including repeated and isolated variables
--   - encoding: an unbounded subset of the natural numbers → a Set ℕ satisfying Set.Infinite; reason: for subsets of ℕ, infinitude and unboundedness are equivalent
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), canonical source.pdf, SHA-256 9eeb0875db685945a8b4c78bc4d30bfdbf3289a943d06f464836530d0eb22467. p.24, Proposition 4.11; proof pp.26–27, with uniform witnesses specified on p.27.

import Definitions.Def_StabilityDichotomies_Approximability_Core
import Definitions.Def_StabilityDichotomies_Solvability_Supplement_FourParity

open scoped Classical

namespace StabilityDichotomies.Solvability.Supplement

/-- Proposition 4.11, p.24 (proof pp.26–27). The witnesses are uniform in the solver and size;
no code family or desired hard-instance property is a hypothesis. -/
theorem parity_approximation_lower :
    ∃ ε₀ c₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ 0 < c₀ ∧
      ∃ D₀ : ℕ, 1 ≤ D₀ ∧ ∃ N₀ : Set ℕ, N₀.Infinite ∧
        ∀ A : Solver parityLanguage, Approximates A ε₀ →
          ∀ n ∈ N₀, ∃ I : Instance parityLanguage (Fin n),
            Satisfiable I ∧ I.constraints.card ≤ D₀ * n ∧
              c₀ * (n : ℝ) ≤ averageSensitivity A I := by sorry

end StabilityDichotomies.Solvability.Supplement
