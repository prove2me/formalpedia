-- Prove2me | Theorems.Thm_SecretaryAdvice_BinaryLimit_dual_closed_form_late
-- name    : SecretaryAdvice.BinaryLimit.dual_closed_form_late
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:28.48998+00:00
-- url     : https://prove2.me/theorems/33798ebc-fecd-443d-8f9f-b5736693d048
-- title:
--   Proof of Theorem 20, p. 21 — late dual coordinates
-- statement:
--   Let $n\ge1$, $p,p'\in[1/2,1]$, and let $t_N$ be the first positive $N$ coordinate of the rescaled greedy dual. For each $t_N\le i\le n$,
--
--   $$w_i^Y=p-\sum_{j=i}^{n-1}\frac{1-p'}j,\qquad w_i^N=1-p-\sum_{j=i}^{n-1}\frac{p'}j.$$
--
--   The formulas describe the late part of the dual exactly; an empty sum at $i=n$ is zero. When $p=1$, $t_N=n+1$, so this range is empty.
--
--   **Formalization Note** Times are 1-based natural numbers. The threshold is defined by positivity of the greedy coordinate.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 21, proof of Theorem 20, closed-form display

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual

namespace SecretaryAdvice.BinaryLimit

theorem dual_closed_form_late (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1)
    (i : ℕ) (hi : tN n p pp ≤ i) (hin : i ≤ n) :
    w n p pp i true = p - (∑ j ∈ Finset.Ico i n, (1 - pp) / (j : ℝ)) ∧
    w n p pp i false = (1 - p) - (∑ j ∈ Finset.Ico i n, pp / (j : ℝ)) := by sorry

end SecretaryAdvice.BinaryLimit
