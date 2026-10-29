-- Prove2me | Theorems.Thm_PeskirShiryaev_AmericanPut_early_exercise_premium
-- name    : PeskirShiryaev.AmericanPut.early_exercise_premium
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:41.060016+00:00
-- url     : https://prove2.me/theorems/ecc20ab3-0498-427b-bb1d-e5a9aad2de26
-- title:
--   Eq. (25.2.36) — early-exercise premium representation
-- statement:
--   In the geometric Brownian American put model, for every $t\in[0,T]$ and $x>0$, let $b$ be the stopping-set boundary and $G(y)=(K-y)^+$. Then
--   $$V(t,x)=e^{-r(T-t)}E[G(X_{T-t}^x)]+rK\int_0^{T-t}e^{-ru}P(X_u^x\le b(t+u))\,du.$$
--   The first term is the European put value. The second is the additional value of the right to exercise before maturity.
--
--   **Formalization Note** Elapsed-time stock $X_s^x$ represents the book's $X_{t+s}$ under $P_{t,x}$. The theorem includes $t=T$, where the integral vanishes. It assumes neither the premium identity nor global $C^{1,2}$ regularity across the exercise boundary.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 385 (PDF 401), Eq. (25.2.36), final equality

import Definitions.Def_PeskirShiryaev_AmericanPut_Kernels

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace PeskirShiryaev.AmericanPut

theorem early_exercise_premium {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t x : ℝ) (ht : t ∈ Set.Icc 0 M.T) (hx : 0 < x) :
    M.value t x =
      Real.exp (-M.r * (M.T - t)) *
        (∫ ω, M.payoff (M.stock x (M.T - t).toNNReal ω) ∂M.P) +
      M.r * M.K * (∫ u in (0 : ℝ)..(M.T - t), Real.exp (-M.r * u) *
        (M.P {ω | M.stock x u.toNNReal ω ≤ M.boundary (t + u)}).toReal) := by sorry

end PeskirShiryaev.AmericanPut
