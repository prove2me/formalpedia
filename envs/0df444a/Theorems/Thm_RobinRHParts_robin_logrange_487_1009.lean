-- Prove2me | Theorems.Thm_RobinRHParts_robin_logrange_487_1009
-- name    : RobinRHParts.robin_logrange_487_1009
-- status  : Open
-- author  : @xuanji
-- created : 2026-11-24T03:09:07.711182+00:00
-- url     : https://prove2.me/theorems/84d5539c-6256-4c17-90d8-917fdfd8beca
-- title:
--   Robin's inequality for $487 \le \log n < 1009$
-- statement:
--   For every integer $n$ with $487 \le \log n < 1009$ one has $$\sigma(n) < e^{\gamma}\, n \log\log n.$$ (Unconditional.)
-- source:
--   G. Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann, J. Math. Pures Appl. 63 (1984) 187-213; K. Broughan, Equivalents of the Riemann Hypothesis Vol. 1 (Robin's criterion)

import Mathlib

namespace RobinRHParts
theorem robin_logrange_487_1009 :
    ∀ n : ℕ, (487:ℝ) ≤ Real.log n → Real.log n < 1009 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by sorry
end RobinRHParts
