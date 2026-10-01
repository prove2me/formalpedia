-- Prove2me | Theorems.Thm_SmaleMeanValue_dubinin_sugawa_dual
-- name    : SmaleMeanValue.dubinin_sugawa_dual
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:35:55.084624+00:00
-- url     : https://prove2.me/theorems/6e3d348e-ff3e-4337-8668-ea0939c111da
-- title:
--   Dubinin–Sugawa (2009): the dual mean value inequality
-- statement:
--   Let $P$ be a complex polynomial of degree $n \ge 2$ and let $z \in \mathbb C$ with $P'(z) \neq 0$. Then there is a critical point $c$ of $P$ with
--
--   $$
--   \left| \frac{P(z) - P(c)}{z - c} \right| \ge \frac{|P'(z)|}{n\,4^n}.
--   $$
--
--   This is the reverse of the mean value inequality; optimizing the constant $\frac{1}{n4^n}$ is the dual mean value problem.
-- source:
--   Wikipedia, "Mean value problem", revision oldid=1374678764, https://en.wikipedia.org/w/index.php?title=Mean_value_problem&oldid=1374678764, section "Partial results" (Dubinin–Sugawa, reverse inequality); Dubinin, Sugawa, Proc. Japan Acad. Ser. A 85(9) (2009), 135–137, https://arxiv.org/abs/0906.4605

import Mathlib
open Polynomial

namespace SmaleMeanValue

theorem dubinin_sugawa_dual (P : ℂ[X]) (hP : 2 ≤ P.natDegree) (z : ℂ)
    (hz : P.derivative.eval z ≠ 0) :
    ∃ c : ℂ, P.derivative.eval c = 0 ∧
      ‖P.derivative.eval z‖ / ((P.natDegree : ℝ) * 4 ^ P.natDegree) ≤
        ‖(P.eval z - P.eval c) / (z - c)‖ := by sorry

end SmaleMeanValue
