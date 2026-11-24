-- Prove2me | Theorems.Thm_RobinRHParts_robin_direct_17041_22027
-- name    : RobinRHParts.robin_direct_17041_22027
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T03:09:10.579114+00:00
-- url     : https://prove2.me/theorems/a356f768-5c60-4aff-8dad-d3d53639dda2
-- title:
--   Robin's inequality for $17041 \le n < 22027$
-- statement:
--   For every integer $n$ with $17041 \le n < 22027$ one has $$\sigma(n) < e^{\gamma}\, n \log\log n.$$ (A finite verification range of Robin's inequality.)
-- source:
--   G. Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann, J. Math. Pures Appl. 63 (1984) 187-213; K. Broughan, Equivalents of the Riemann Hypothesis Vol. 1 (Robin's criterion)

import Mathlib

namespace RobinRHParts
theorem robin_direct_17041_22027 :
    ∀ n : ℕ, 17041 ≤ n → n < 22027 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by sorry
end RobinRHParts
