-- Prove2me | Theorems.Thm_PeskirShiryaev_AmericanPut_smooth_fit
-- name    : PeskirShiryaev.AmericanPut.smooth_fit
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:36.343389+00:00
-- url     : https://prove2.me/theorems/e2dc9c22-bf0c-49a4-9778-ce01161ede78
-- title:
--   Eq. (25.2.28) — smooth fit at the exercise boundary
-- statement:
--   Let $V$ be the geometric Brownian American put value and $b$ its stopping-set boundary. At every calendar time $0\le t<T$, the spatial derivative exists at the exercise boundary and satisfies
--   $$\frac{\partial V}{\partial x}(t,b(t))=-1.$$
--   This is the smooth-fit condition matching the derivative of the payoff below the boundary to that of the continuation value above it.
--
--   **Formalization Note** The statement uses existence of a two-sided derivative, not Lean's default-valued derivative operator. Maturity is excluded: $V(T,x)=(K-x)^+$ has a corner at $x=K=b(T)$.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 381–382, 384–385 (PDF 397–398, 400–401), Eq. (25.2.28)

import Definitions.Def_PeskirShiryaev_AmericanPut_Boundary

open scoped NNReal ENNReal

namespace PeskirShiryaev.AmericanPut

theorem smooth_fit {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t : ℝ) (ht : t ∈ Set.Ico 0 M.T) :
    HasDerivAt (M.value t) (-1) (M.boundary t) := by sorry

end PeskirShiryaev.AmericanPut
