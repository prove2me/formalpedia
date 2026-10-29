-- Prove2me | Theorems.Thm_PeskirShiryaev_UltimateMaximum_candidate_equations
-- name    : PeskirShiryaev.UltimateMaximum.candidate_equations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:13.064592+00:00
-- url     : https://prove2.me/theorems/2aa7369f-c085-44ad-bfc9-b361bf2135bc
-- title:
--   Eq. (30.1.27) — exact root, ODE and smooth fit
-- statement:
--   Let $\varphi,\Phi$ be the standard normal density and CDF, $F=4\Phi-3$, and $z_*=\inf\{z\ge0:4\Phi(z)-2z\varphi(z)-3=0\}$. Then $z_*>0$ and it is the unique real root of
--   $$4\Phi(z)-2z\varphi(z)-3=0.$$
--   For the even candidate $W(z)=\Phi(z_*)(1+z^2)-|z|\varphi(|z|)+(1-z^2)\Phi(|z|)-3/2$ when $|z|\le z_*$, extended by zero outside, $W$ is continuously differentiable on the real line, twice differentiable inside $(-z_*,z_*)$, and
--   $$W''(z)+zW'(z)-2W(z)=-F(|z|)\quad (|z|<z_*),$$
--   $$W(\pm z_*)=W'(\pm z_*)=0,\qquad W'(0)=0.$$
--   These are the analytic candidate's free-boundary conditions. They do not define it as the stopping value or assert verification against an infimum.
--
--   **Formalization Note** The second derivative is the derivative of the first derivative, and its existence is explicit on the continuation interval; no second differentiability is asserted at the boundary. The root is exact, not the decimal printed for illustration.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 445 (PDF p. 461), Eq. (30.1.27) with Eqs. (30.1.24)–(30.1.25); p. 444 / PDF 460, Eqs. (30.1.21)–(30.1.23)

import Mathlib
import Definitions.Def_PeskirShiryaev_UltimateMaximum_gaussianBoundary

open Set

namespace PeskirShiryaev.UltimateMaximum

theorem candidate_equations :
    0 < criticalLevel ∧ rootEquation criticalLevel = 0 ∧
    (∀ z : ℝ, rootEquation z = 0 → z = criticalLevel) ∧
    ContDiff ℝ 1 candidate ∧
    (∀ z : ℝ, |z| < criticalLevel →
      DifferentiableAt ℝ (deriv candidate) z ∧
      deriv (deriv candidate) z + z * deriv candidate z - 2 * candidate z =
        -runningCost |z|) ∧
    candidate criticalLevel = 0 ∧ candidate (-criticalLevel) = 0 ∧
    deriv candidate criticalLevel = 0 ∧ deriv candidate (-criticalLevel) = 0 ∧
    deriv candidate 0 = 0 := by sorry

end PeskirShiryaev.UltimateMaximum

/- Imported definition bodies (verbatim code, for standalone inspection):

namespace PeskirShiryaev.UltimateMaximum

noncomputable def phi (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)

noncomputable def Phi (x : ℝ) : ℝ := ∫ y in Iic x, phi y

noncomputable def runningCost (x : ℝ) : ℝ := 4 * Phi x - 3

noncomputable def rootEquation (z : ℝ) : ℝ := 4 * Phi z - 2 * z * phi z - 3

noncomputable def criticalLevel : ℝ := sInf {z : ℝ | 0 ≤ z ∧ rootEquation z = 0}

noncomputable def candidate (z : ℝ) : ℝ :=
  if |z| ≤ criticalLevel then
    Phi criticalLevel * (1 + z ^ 2) - |z| * phi |z| +
      (1 - z ^ 2) * Phi |z| - 3 / 2
  else 0

end PeskirShiryaev.UltimateMaximum
-/
