-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P31_square_torus_green
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P31.square_torus_green
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:41:00.772338+00:00
-- url     : https://prove2.me/theorems/892d0b69-e791-49a4-9c61-f9632c9e3813
-- title:
--   Square-torus inverse Laplacian: theta formula and Fourier normalization
-- statement:
--   Let $G_T$ be the inverse Laplacian on the square torus of side $2\pi$, with its constant mode removed. Construct it independently by integrating the torus heat kernel $K_s$:
--
--   $$G_T(x,y)=\int_0^\infty\left(K_s(x,y)-\frac1{4\pi^2}\right)\,ds,\qquad K_s(x,y)=\frac1{4\pi^2}\sum_{(k,l)\in\mathbb Z^2}e^{-s(k^2+l^2)}\cos(kx+ly).$$
--
--   For $(x,y)\notin(2\pi\mathbb Z)^2$, this integral converges and
--
--   $$G_T(x,y)=-\frac1{2\pi}\left[\log\left|\theta_1\left(\frac{x+iy}{2\pi},i\right)\right|-\frac{y^2}{4\pi}-\log\eta(i)\right].$$
--
--   Here $\theta_1$ is the odd Jacobi theta function with first argument of period one, and $\eta(i)>0$ is the Dedekind eta value. The kernel is integrable on a torus cell. Its normalized Fourier coefficient is zero at $(k,l)=(0,0)$ and $[4\pi^2(k^2+l^2)]^{-1}$ otherwise. The heat and theta series are asserted to converge on their stated domains.
--
--   This identifies the Green function used in the geometric coefficients without defining it by the identity being asserted.
-- source:
--   Entanglement Entropy in the O(N) model, arXiv:0904.4477v1, PDF p. 27, §V A (5.13)–(5.14): zero-mean square-torus Green function

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P31

noncomputable section

open Filter Set MeasureTheory

open scoped Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P31

/-- PDF p.27, (5.13)--(5.14): the independently constructed torus inverse
Laplacian has the theta expression and zero constant Fourier mode. The
nonzero Fourier coefficients are `1/(4*pi^2*|k|^2)` with normalized torus
measure. Summability and integrability conclusions prevent default `tsum`
and Bochner-integral values from replacing the kernels. -/
theorem square_torus_green :
    (∀ s : ℝ, 0 < s → ∀ x y : ℝ,
      Summable (fun k : ℤ × ℤ =>
        Real.exp (-s * ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2)) *
          Real.cos ((k.1 : ℝ) * x + (k.2 : ℝ) * y))) ∧
    (∀ z : ℂ, Summable (fun j : ℕ => (-1 : ℂ) ^ j *
      (Real.exp (-Real.pi * ((j : ℝ) + 1 / 2) ^ 2) : ℂ) *
        Complex.sin (((2 * j + 1 : ℕ) : ℂ) * (Real.pi : ℂ) * z))) ∧
    0 < etaAtI ∧
    (∀ x y : ℝ, OffSquareLattice x y →
      IntegrableOn (fun s : ℝ => squareHeat s x y - 1 / (4 * Real.pi ^ 2))
        (Ioi 0) ∧
      oddThetaAtI (((x : ℂ) + Complex.I * (y : ℂ)) / (2 * (Real.pi : ℂ))) ≠ 0 ∧
      squareGreen x y = -(1 / (2 * Real.pi)) *
        (Real.log ‖oddThetaAtI (((x : ℂ) + Complex.I * (y : ℂ)) /
          (2 * (Real.pi : ℂ)))‖ - y ^ 2 / (4 * Real.pi) - Real.log etaAtI)) ∧
    IntegrableOn (fun xy : ℝ × ℝ => squareGreen xy.1 xy.2)
      ((Icc (0 : ℝ) (2 * Real.pi)) ×ˢ (Icc (0 : ℝ) (2 * Real.pi))) ∧
    (∀ k l : ℤ,
      (1 / (4 * (Real.pi : ℂ) ^ 2)) *
        (∫ x in Icc (0 : ℝ) (2 * Real.pi),
          ∫ y in Icc (0 : ℝ) (2 * Real.pi),
            (squareGreen x y : ℂ) * Complex.exp
              (-Complex.I * (((k : ℝ) * x + (l : ℝ) * y : ℝ) : ℂ))) =
        if k = 0 ∧ l = 0 then 0 else
          ((1 / (4 * Real.pi ^ 2 * ((k : ℝ) ^ 2 + (l : ℝ) ^ 2)) : ℝ) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P31

end
