-- Prove2me | Theorems.Thm_SecretaryAdvice_BinaryLimit_dual_recursion
-- name    : SecretaryAdvice.BinaryLimit.dual_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:18.376084+00:00
-- url     : https://prove2.me/theorems/ee331e42-99b4-440a-a228-16d5a32a2a15
-- title:
--   Proof of Theorem 20, p. 21 — early Y recursion
-- statement:
--   Let $n\ge1$ and $p,p'\in[1/2,1]$. Between the first positive $Y$ coordinate and two times before the first positive $N$ coordinate, the rescaled greedy dual satisfies
--
--   $$w_i^Y=\frac{i+p'}i\,w_{i+1}^Y-\frac pi\qquad(t_Y\le i\le t_N-2).$$
--
--   This exact recursion is the finite starting point for the $Y$ threshold asymptotics.
--
--   **Formalization Note** The printed derivation says “for $i<t_N$.” It drops $w_{i+1}^N$ and removes the maximum, so the displayed identity applies on $t_Y\le i\le t_N-2$; it fails in general at $i=t_N-1$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 21, proof of Theorem 20, recursion display

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual

namespace SecretaryAdvice.BinaryLimit

theorem dual_recursion (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1)
    (i : ℕ) (hi0 : 1 ≤ i) (hY : tY n p pp ≤ i) (hN : i + 1 < tN n p pp) :
    w n p pp i true = ((i : ℝ) + pp) / (i : ℝ) * w n p pp (i + 1) true - p / (i : ℝ) := by sorry

end SecretaryAdvice.BinaryLimit
