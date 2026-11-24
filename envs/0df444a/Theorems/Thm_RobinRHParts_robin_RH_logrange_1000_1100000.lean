-- Prove2me | Theorems.Thm_RobinRHParts_robin_RH_logrange_1000_1100000
-- name    : RobinRHParts.robin_RH_logrange_1000_1100000
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T03:09:08.459649+00:00
-- url     : https://prove2.me/theorems/6ec49185-e2f9-409b-8a07-6d41ebe4d8bf
-- title:
--   Under RH, Robin's inequality for $1000 \le \log n < 1.1\cdot 10^6$
-- statement:
--   Assume the Riemann hypothesis. Then for every integer $n$ with $1000 \le \log n < 1100000$ one has $$\sigma(n) < e^{\gamma}\, n \log\log n.$$
-- source:
--   G. Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann, J. Math. Pures Appl. 63 (1984) 187-213; K. Broughan, Equivalents of the Riemann Hypothesis Vol. 1 (Robin's criterion)

import Mathlib

namespace RobinRHParts
theorem robin_RH_logrange_1000_1100000 (hRH : RiemannHypothesis) :
    ∀ n : ℕ, (1000:ℝ) ≤ Real.log n → Real.log n < 1100000 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by sorry
end RobinRHParts
