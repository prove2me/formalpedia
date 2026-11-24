-- Prove2me | Theorems.Thm_RobinRHParts_robin_RH_log_ge_1100000
-- name    : RobinRHParts.robin_RH_log_ge_1100000
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T03:09:06.589559+00:00
-- url     : https://prove2.me/theorems/342d6de3-2789-444a-880a-212db2610df8
-- title:
--   Under RH, Robin's inequality for $\log n \ge 1.1\cdot 10^6$
-- statement:
--   Assume the Riemann hypothesis. Then for every integer $n$ with $\log n \ge 1100000$ one has $$\sigma(n) < e^{\gamma}\, n \log\log n.$$
-- source:
--   G. Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann, J. Math. Pures Appl. 63 (1984) 187-213; K. Broughan, Equivalents of the Riemann Hypothesis Vol. 1 (Robin's criterion)

import Mathlib

namespace RobinRHParts
theorem robin_RH_log_ge_1100000 (hRH : RiemannHypothesis) :
    ∀ n : ℕ, (1100000:ℝ) ≤ Real.log n →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by sorry
end RobinRHParts
