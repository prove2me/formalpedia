-- Prove2me | Theorems.Thm_RobinRHParts_robin_direct_5041_11041
-- name    : RobinRHParts.robin_direct_5041_11041
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T03:09:06.315812+00:00
-- url     : https://prove2.me/theorems/b8d318fc-46ff-4115-b470-0ea766a4d1f0
-- title:
--   Robin's inequality for $5041 \le n < 11041$
-- statement:
--   For every integer $n$ with $5041 \le n < 11041$ one has $$\sigma(n) < e^{\gamma}\, n \log\log n.$$ (A finite verification range of Robin's inequality.)
-- source:
--   G. Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann, J. Math. Pures Appl. 63 (1984) 187-213; K. Broughan, Equivalents of the Riemann Hypothesis Vol. 1 (Robin's criterion)

import Mathlib

namespace RobinRHParts
theorem robin_direct_5041_11041 :
    ∀ n : ℕ, 5041 ≤ n → n < 11041 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by sorry
end RobinRHParts
