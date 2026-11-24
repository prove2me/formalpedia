-- Prove2me | Theorems.Thm_RobinRHParts_robin_direct_11041_17041
-- name    : RobinRHParts.robin_direct_11041_17041
-- status  : Open
-- author  : @xuanji
-- created : 2026-11-24T03:09:05.897172+00:00
-- url     : https://prove2.me/theorems/c992c502-65fb-4021-a37d-1fee98044083
-- title:
--   Robin's inequality for $11041 \le n < 17041$
-- statement:
--   For every integer $n$ with $11041 \le n < 17041$ one has $$\sigma(n) < e^{\gamma}\, n \log\log n.$$ (A finite verification range of Robin's inequality.)
-- source:
--   G. Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann, J. Math. Pures Appl. 63 (1984) 187-213; K. Broughan, Equivalents of the Riemann Hypothesis Vol. 1 (Robin's criterion)

import Mathlib

namespace RobinRHParts
theorem robin_direct_11041_17041 :
    ∀ n : ℕ, 11041 ≤ n → n < 17041 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by sorry
end RobinRHParts
