-- Prove2me | Theorems.Thm_SecretaryAdvice_BinaryLimit_opt_eq_greedy_value
-- name    : SecretaryAdvice.BinaryLimit.opt_eq_greedy_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:22.375471+00:00
-- url     : https://prove2.me/theorems/60b48d09-59be-4299-aaed-ddf5b5e60817
-- title:
--   Appendix C, p. 29 — primal optimum equals the greedy dual objective
-- statement:
--   For $n\ge1$ and classifier recall and specificity $p,p'\in[1/2,1]$, the optimal value of the binary advice primal LP equals the objective value of its rescaled greedy dual solution:
--
--   $$\operatorname{Opt}(n,p,p')=\frac1n\sum_{i=1}^n(w_i^Y+w_i^N).$$
--
--   This identity is the bridge from the primal optimum to the explicit asymptotic analysis. It requires both greedy dual optimality in Appendix C and finite LP duality.
--
--   **Formalization Note** The greedy variables here are $w=n u$, where $u$ denotes the original dual variables on page 20.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 29, proof of Theorem 19 and proof of Theorem 20

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual

namespace SecretaryAdvice.BinaryLimit

theorem opt_eq_greedy_value (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) :
    Opt n p pp = (1 / (n : ℝ)) *
      (∑ i ∈ Finset.Icc 1 n, (w n p pp i true + w n p pp i false)) := by sorry

end SecretaryAdvice.BinaryLimit
