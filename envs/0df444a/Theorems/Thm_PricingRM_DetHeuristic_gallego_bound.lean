-- Prove2me | Theorems.Thm_PricingRM_DetHeuristic_gallego_bound
-- name    : PricingRM.DetHeuristic.gallego_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:33:10.151563+00:00
-- url     : https://prove2.me/theorems/e7a4e382-1e0e-4245-8022-6186080d4a05
-- title:
--   Appendix, inequality (*) — Gallego's bound $E[(X-C)^+] \le \frac12(\sqrt{\sigma^2+(C-EX)^2}-(C-EX))$
-- statement:
--   Let $X$ be a square-integrable real random variable on a probability space, with mean $E X$ and variance $\sigma^2 = \operatorname{Var} X$, and let $C$ be a real number. Then
--   $$
--   E\big[(X - C)^+\big] \le \frac{\sqrt{\sigma^2 + (C - E X)^2} - (C - E X)}{2}.
--   $$
--   Moreover, if $0 < E X \le C$, then with the coefficient of variation $\nu = \sigma / E X$,
--   $$
--   \frac{E[(X - C)^+]}{E X} \le \frac{\sqrt{\sigma^2 + (C - E X)^2} - (C - E X)}{2 E X} \le \frac{\nu}{2}.
--   $$
--
--   This is the distribution-free bound of Gallego (1992) on the expected excess of a random variable over a threshold, in terms of its first two moments only. In the paper it is applied to the cumulative demand $X = \mathscr{D}_n^{\det}$ with $C = C_0$: it turns the expected lost sales of the deterministic-price heuristic into the quantity $\eta_n^{\det}(C_0)$ of eq. (34), and, since $E[\mathscr{D}_N^{\det}] \le C_0$, into $\nu(C_0)/2$.
--
--   **Formalization Note** The statement is for a general random variable, as Gallego's result is; the paper's (\*) is the instance $X = \mathscr{D}_N^{\det}$, $C = C_0$, with $\sigma^2$ in its numerator meaning $\sigma_N^2$. Square integrability (`MemLp X 2`) is required because Mathlib's `variance` is $0$ for a random variable of infinite variance.
-- source:
--   Bitran and Caldentey, An Overview of Pricing Models for Revenue Management, MSOM 5(3) 2003, p. 227, Appendix, Proof of Proposition 8, inequality (*) (citing Gallego 1992)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PricingRM.DetHeuristic

/-- Gallego (1992), as used in the Appendix of Bitran–Caldentey (2003), p. 227, inequality (*):
for a square-integrable random variable `X` and a real `C`,
`E[(X - C)^+] ≤ (√(Var X + (C - E X)^2) - (C - E X)) / 2`; and when `0 < E X ≤ C`, the
normalized chain `E[(X-C)^+]/E X ≤ (√(Var X + (C - E X)^2) - (C - E X)) / (2 E X) ≤ ν/2`
holds with `ν = √(Var X) / E X`. -/
theorem gallego_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (C : ℝ) :
    ∫ ω, max (X ω - C) 0 ∂P ≤
        (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) / 2 ∧
      (0 < ∫ ω, X ω ∂P → ∫ ω, X ω ∂P ≤ C →
        (∫ ω, max (X ω - C) 0 ∂P) / (∫ ω, X ω ∂P) ≤
            (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) /
              (2 * ∫ ω, X ω ∂P) ∧
          (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) /
              (2 * ∫ ω, X ω ∂P) ≤
            (Real.sqrt (variance X P) / ∫ ω, X ω ∂P) / 2) := by sorry

end PricingRM.DetHeuristic
