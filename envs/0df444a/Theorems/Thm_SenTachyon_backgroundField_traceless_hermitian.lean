-- Prove2me | Theorems.Thm_SenTachyon_backgroundField_traceless_hermitian
-- name    : SenTachyon.backgroundField_traceless_hermitian
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:00:19.02718+00:00
-- url     : https://prove2.me/theorems/619bb92a-e8f2-4801-8452-c89583362b30
-- title:
--   Remark after eq. (7): the background field lies in the SU(2) part
-- statement:
--   Let $\tilde R_1,\tilde R_2>0$ be the radii of the dual torus and let $A$ be the background gauge field (4): $A_1=0$, $A_2=2\pi x^1\sigma_3/\tilde V$ with $\tilde V=4\pi^2\tilde R_1\tilde R_2$. Then for each $\mu\in\{1,2\}$ and every point $x$,
--   $$\operatorname{tr}A_\mu(x)=0\qquad\text{and}\qquad A_\mu(x)^\dagger=A_\mu(x).$$
--
--   That is, the configuration lies entirely in the $\mathfrak{su}(2)$ part of the $\mathfrak u(2)$ gauge algebra and has no $U(1)$ component.
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, p. 2, first sentence after eq. (7)

import Mathlib
import Definitions.Def_SenTachyon_Defs

open scoped ContDiff
open Filter Topology

namespace SenTachyon
theorem backgroundField_traceless_hermitian (R₁t R₂t : ℝ) (h₁ : 0 < R₁t) (h₂ : 0 < R₂t)
    (μ : Fin 2) (x : ℝ × ℝ) :
    (backgroundField R₁t R₂t μ x).trace = 0 ∧ (backgroundField R₁t R₂t μ x).IsHermitian := by sorry
end SenTachyon
