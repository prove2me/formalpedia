-- Prove2me | Theorems.Thm_SecretaryAdvice_Binary_greedy_monotone
-- name    : SecretaryAdvice.Binary.greedy_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:38.146684+00:00
-- url     : https://prove2.me/theorems/7f124e22-3aa1-4eeb-9e8a-5eb6e31af8ab
-- title:
--   Appendix C, p. 29 — binary greedy dual variables are non-decreasing
-- statement:
--   Let $u_i^s$ be the binary-classifier dual vector constructed by the backward recurrence in equation (10). For each signal $s\in\{Y,N\}$ and each adjacent pair of rounds $1\leq i<n$,
--
--   $$u_i^s\leq u_{i+1}^s.$$
--
--   This monotonicity is one of the two dual properties required by Proposition 12 to obtain a threshold policy.
--
--   **Formalization Note** The theorem uses the exact finite greedy vector, including the maximum with zero, and the model's ranges $p,p'\in[1/2,1]$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 29, Appendix C, first paragraph

import Mathlib
import Definitions.Def_SecretaryAdvice_Binary_LP

namespace SecretaryAdvice.Binary

/-- Appendix C, p. 29: the greedy dual variables increase with round number. -/
theorem greedy_monotone (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ)
    (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hp'0 : (1 / 2 : ℝ) ≤ p') (hp'1 : p' ≤ 1) :
    ∀ i : ℕ, 1 ≤ i → i < n → ∀ s : Bool,
      greedy n p p' i s ≤ greedy n p p' (i + 1) s := by sorry

end SecretaryAdvice.Binary
