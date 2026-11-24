-- Prove2me | Theorems.Thm_RobinRHParts_robin_logrange_10_487
-- name    : RobinRHParts.robin_logrange_10_487
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T03:09:07.163671+00:00
-- url     : https://prove2.me/theorems/b922a467-4a94-4690-b9a9-f297ef644bf2
-- title:
--   Robin's inequality for $10 \le \log n < 487$
-- statement:
--   For every integer $n$ with $10 \le \log n < 487$ one has $$\sigma(n) < e^{\gamma}\, n \log\log n.$$ (Unconditional.)
-- source:
--   G. Robin, Grandes valeurs de la fonction somme des diviseurs et hypothese de Riemann, J. Math. Pures Appl. 63 (1984) 187-213; K. Broughan, Equivalents of the Riemann Hypothesis Vol. 1 (Robin's criterion)

import Mathlib

namespace RobinRHParts
theorem robin_logrange_10_487 :
    ∀ n : ℕ, (10:ℝ) ≤ Real.log n → Real.log n < 487 →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by sorry
end RobinRHParts
