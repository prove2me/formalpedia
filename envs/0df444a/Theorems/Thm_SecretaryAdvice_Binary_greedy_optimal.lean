-- Prove2me | Theorems.Thm_SecretaryAdvice_Binary_greedy_optimal
-- name    : SecretaryAdvice.Binary.greedy_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:40.443003+00:00
-- url     : https://prove2.me/theorems/0b352351-5229-4b60-8a8c-7f0eaa98bbbb
-- title:
--   Appendix C, p. 29 — binary greedy vector minimizes the dual LP
-- statement:
--   Let $u$ be the binary-classifier greedy dual vector of equation (10). It satisfies every nonnegativity and dual LP constraint, and among all feasible dual vectors $v$ it minimizes the objective:
--
--   $$\sum_{i=1}^n(u_i^Y+u_i^N)\leq\sum_{i=1}^n(v_i^Y+v_i^N).$$
--
--   This identifies the dual certificate used in the threshold-optimality argument.
--
--   **Formalization Note** The theorem quantifies over all dual-feasible vectors, with constraints only on rounds $1,\ldots,n$. No optimal vector is assumed to exist as an extra hypothesis.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 29, Appendix C, final paragraph

import Mathlib
import Definitions.Def_SecretaryAdvice_Binary_LP

namespace SecretaryAdvice.Binary

/-- Appendix C, p. 29: equation (10) gives a feasible, minimum-value dual vector. -/
theorem greedy_optimal (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ)
    (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hp'0 : (1 / 2 : ℝ) ≤ p') (hp'1 : p' ≤ 1) :
    DualFeasible n p p' (greedy n p p') ∧
    ∀ u : ℕ → Bool → ℝ, DualFeasible n p p' u →
      dualValue n (greedy n p p') ≤ dualValue n u := by sorry

end SecretaryAdvice.Binary
