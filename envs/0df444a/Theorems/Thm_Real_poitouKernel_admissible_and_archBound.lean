-- Prove2me | Theorems.Thm_Real_poitouKernel_admissible_and_archBound
-- name    : Real.poitouKernel_admissible_and_archBound
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/7eecb2e9-fd88-59e3-a23e-005e04c6559b
-- title:
--   Properties of Poitou's kernel e^{-11x^2/100}/cosh(x/2)
-- statement:
--   For the explicit function $F:\mathbb{R}\to\mathbb{R}$, $F(x)=e^{-(11/100)x^2}/\cosh(x/2)$, the theorem asserts a conjunction of nine clauses, with no hypotheses: (i) $F$ is differentiable on $\mathbb{R}$; (ii) $F$ is even, $F(-x)=F(x)$ for all real $x$; (iii) $F(0)=1$; (iv) $F(x)\ge 0$ for all $x$; (v) there exist $c,\varepsilon>0$ with $|F(x)|\le c\,e^{-(1/2+\varepsilon)|x|}$ for all $x$; (vi) for every $\rho\in\mathbb{C}$ with $0<\operatorname{Re}\rho<1$ the integral $\int_{\mathbb{R}}F(x)\,e^{(\operatorname{Re}\rho-1/2)x}\cos(\operatorname{Im}\rho\cdot x)\,dx$ is nonnegative; (vii) $F$ is $C^2$; (viii) there exist $c,\varepsilon>0$ such that for each $k\in\{0,1,2\}$ and all $x$, $|F^{(k)}(x)|\le c\,e^{-(1/2+\varepsilon)|x|}$, where $F^{(k)}$ is the $k$-th iterated derivative; (ix) $2\int_0^\infty F(x)\,(e^{x/2}+e^{-x/2})\,dx=2\sqrt{100\pi/11}$; and (x) the numerical inequality $$\log(9805/2000)+\tfrac1{12}\sqrt{100\pi/11}\ \le\ \gamma+\log(4\pi)-\int_0^\infty\frac{1-F(x)}{e^{x/2}-e^{-x/2}}\,dx,$$ with $\gamma$ the Euler–Mascheroni constant. All integrals are Bochner integrals over $\mathbb{R}$ or over $(0,\infty)$ in the sense of Mathlib's measure-theoretic integral.
--
--   These are the concrete analytic facts about Poitou's test kernel with parameter $y_0=11/100$ that feed the explicit-formula (Odlyzko) method: clauses (i)–(viii) are the admissibility and strip-positivity conditions on the kernel, clause (ix) evaluates the contribution of the pole of the Dedekind zeta function, and clause (x) is the archimedean estimate with the numerical constant $9.805$. The statement is used to derive the unconditional discriminant lower bound for totally complex number fields of degree at least $24$, via [`NumberField.odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank`](thm.html#NumberField.odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Real_poitouKernel_admissible_and_archBound.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Real.poitouKernel_admissible_and_archBound :
    let F : ℝ → ℝ := fun x => Real.exp (-(11 / 100) * x ^ 2) / Real.cosh (x / 2)

    Differentiable ℝ F ∧ (∀ x : ℝ, F (-x) = F x) ∧ F 0 = 1 ∧ (∀ x : ℝ, 0 ≤ F x) ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧

    (∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      0 ≤ ∫ x : ℝ, F x * Real.exp ((ρ.re - 1 / 2) * x) * Real.cos (ρ.im * x)) ∧

    ContDiff ℝ 2 F ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧

    (2 * ∫ x in Set.Ioi (0 : ℝ), F x * (Real.exp (x / 2) + Real.exp (-(x / 2)))
        = 2 * Real.sqrt (100 * Real.pi / 11)) ∧

    (Real.log (9805 / 2000) + (1 / 12) * Real.sqrt (100 * Real.pi / 11)
      ≤ Real.eulerMascheroniConstant + Real.log (4 * Real.pi)
          - ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2)))) := by sorry
