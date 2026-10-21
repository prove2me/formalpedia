-- Prove2me | Theorems.Thm_PostTradeFees_Welfare_appendix_A3
-- name    : PostTradeFees.Welfare.appendix_A3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:02.31726+00:00
-- url     : https://prove2.me/theorems/660d3500-33d2-4785-be8f-108e1ce67066
-- title:
--   Equation (A3), Appendix pp. 1–2 (PDF 29–30) — stationary trading-state distributions
-- statement:
--   For $N>1$, the "all" and "own" order-flow chains have unique stationary probability distributions. In the order limit order, internalized market order, non-internalized market order, they are
--
--   $$
--   \varphi_{k,\mathrm{all}}=\left(\frac23,\frac1{3N},\frac{N-1}{3N}\right),\qquad
--   \varphi_{TS,\mathrm{own}}=\left(\frac{2N}{2N+1},\frac1{2N+1},0\right).
--   $$
--
--   These distributions convert trading strategies into long-run trading rates and expected welfare.
--
--   **Formalization Note** The "own" chain sends its unreachable third state back to the limit-order state; the paper prints a zero row in (A2), inconsistent with its stochastic-matrix convention. The stationary distribution is unchanged.
-- source:
--   Degryse, Van Achter & Wuyts, Plumbing of Securities Markets, SSRN 2023597 (version of October 2016), Appendix pp. 1–2 (PDF 29–30), Equations (A1)–(A3)

import Mathlib
import Definitions.Def_PostTradeFees_Welfare_Model

namespace PostTradeFees.Welfare

/-- Equation (A3): the two unique stationary distributions. -/
theorem appendix_A3 (N : ℕ) (hN : 1 < N) :
    (∀ φ : Fin 3 → ℝ,
      MarkovChain.IsStationary (chainAll N) φ ↔
        φ = ![(2 / 3 : ℝ), 1 / (3 * (N : ℝ)), ((N : ℝ) - 1) / (3 * (N : ℝ))]) ∧
    (∀ φ : Fin 3 → ℝ,
      MarkovChain.IsStationary (chainOwn N) φ ↔
        φ = ![2 * (N : ℝ) / (2 * (N : ℝ) + 1),
               1 / (2 * (N : ℝ) + 1), (0 : ℝ)]) := by sorry

end PostTradeFees.Welfare
