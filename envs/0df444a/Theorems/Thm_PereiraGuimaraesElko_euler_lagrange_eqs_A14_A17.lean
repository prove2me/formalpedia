-- Prove2me | Theorems.Thm_PereiraGuimaraesElko_euler_lagrange_eqs_A14_A17
-- name    : PereiraGuimaraesElko.euler_lagrange_eqs_A14_A17
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:48:57.534326+00:00
-- url     : https://prove2.me/theorems/3689aa03-b7dd-431c-9299-4a611d145f0c
-- title:
--   Eqs. (A.14)–(A.17): Euler–Lagrange equations of the Elko minisuperspace Lagrangian (A.13)
-- statement:
--   Fix a constant $\kappa\neq0$ (with $\kappa^2=8\pi G$) and a differentiable potential $V:\mathbb R\to\mathbb R$. Let $\mathcal L$ be the Lagrangian (A.13) of the Elko field $\Phi$ coupled to a flat FRW metric with lapse $N$, scale factor $a$ and torsion functions $h,f$:
--   $$
--   \mathcal L=-\frac1N\left(\frac{3a\dot a^2}{\kappa^2}-\frac{3a^3h^2}{\kappa^2}-\frac12a^3\dot\Phi^2-\frac38a(\dot a+ah)^2\Phi^2\right)-N\left(\frac{3a^3f^2}{\kappa^2}+\frac38a^3f^2\Phi^2+a^3V(\Phi)\right),
--   $$
--   viewed as a function of the seven real slots $(N,a,\dot a,\Phi,\dot\Phi,h,f)$.
--
--   Let $I\subseteq\mathbb R$ be an open set of times and $a,\Phi,h,f$ real functions of time such that on $I$: $a>0$; $a,\dot a,\Phi,\dot\Phi,h$ are differentiable; and, in the gauge $N\equiv1$, the five Euler–Lagrange equations hold:
--
--   1. $\partial\mathcal L/\partial N=0$ (evaluated at $N=1$);
--   2. $\frac{d}{dt}\,\partial\mathcal L/\partial\dot a-\partial\mathcal L/\partial a=0$;
--   3. $\frac{d}{dt}\,\partial\mathcal L/\partial\dot\Phi-\partial\mathcal L/\partial\Phi=0$;
--   4. $\partial\mathcal L/\partial h=0$;
--   5. $\partial\mathcal L/\partial f=0$.
--
--   Then, with $H=\dot a/a$, at every $t\in I$:
--   $$
--   3H^2=\kappa^2\left[\frac{\dot\Phi^2}{2}+V(\Phi)+\frac38H^2\Phi^2+\frac34Hh\Phi^2\right]+3\left(1+\tfrac18\kappa^2\Phi^2\right)h^2+3\left(1+\tfrac18\kappa^2\Phi^2\right)f^2,\qquad\text{(A.14)}
--   $$
--   $$
--   -2\dot H-3H^2=\kappa^2\left[\frac{\dot\Phi^2}{2}-V(\Phi)-\frac38H^2\Phi^2-\frac14\frac{d}{dt}\big[(H+h)\Phi^2\big]\right]+3\left(1+\tfrac18\kappa^2\Phi^2\right)h^2-3\left(1+\tfrac18\kappa^2\Phi^2\right)f^2,\qquad\text{(A.15)}
--   $$
--   $$
--   \ddot\Phi+3H\dot\Phi+V'(\Phi)-\frac34\left((H+h)^2-f^2\right)\Phi=0,\qquad\text{(A.16)}
--   $$
--   $$
--   h=-\frac18\,\frac{\kappa^2\Phi^2}{1+\kappa^2\Phi^2/8}\,\frac{\dot a}{a},\qquad f=0.\qquad\text{(A.17)}
--   $$
--
--   These are the field equations of the Einstein–Cartan Elko cosmology from which the whole paper starts.
--
--   **Formalization Note** Partial derivatives of $\mathcal L$ are Lean `deriv`s of $\mathcal L$ in one slot with the other slots frozen at the trajectory values; time derivatives are `deriv` in $t$.
-- source:
--   S. H. Pereira and T. M. Guimarães, "From inflation to recent cosmic acceleration: the fermionic Elko field driving the evolution of the universe", JCAP 09 (2017) 038, https://doi.org/10.1088/1475-7516/2017/09/038 (arXiv:1702.07385), p. 14, Appendix A, Eqs. (A.13)–(A.17)

import Mathlib

namespace PereiraGuimaraesElko

theorem euler_lagrange_eqs_A14_A17 (κ : ℝ) (hκ : κ ≠ 0) (V : ℝ → ℝ) (hV : Differentiable ℝ V)
    (L : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hL : ∀ N a ad Φ Φd h f, L N a ad Φ Φd h f =
      -(1 / N) * (3 * a * ad ^ 2 / κ ^ 2 - 3 * a ^ 3 * h ^ 2 / κ ^ 2 - 1 / 2 * a ^ 3 * Φd ^ 2
        - 3 / 8 * a * (ad + a * h) ^ 2 * Φ ^ 2)
      - N * (3 * a ^ 3 * f ^ 2 / κ ^ 2 + 3 / 8 * a ^ 3 * f ^ 2 * Φ ^ 2 + a ^ 3 * V Φ))
    (I : Set ℝ) (hI : IsOpen I) (a Φ h f : ℝ → ℝ)
    (ha : ∀ t ∈ I, 0 < a t)
    (ha1 : ∀ t ∈ I, DifferentiableAt ℝ a t) (ha2 : ∀ t ∈ I, DifferentiableAt ℝ (deriv a) t)
    (hΦ1 : ∀ t ∈ I, DifferentiableAt ℝ Φ t) (hΦ2 : ∀ t ∈ I, DifferentiableAt ℝ (deriv Φ) t)
    (hh : ∀ t ∈ I, DifferentiableAt ℝ h t)
    (EL_N : ∀ t ∈ I,
      deriv (fun N => L N (a t) (deriv a t) (Φ t) (deriv Φ t) (h t) (f t)) 1 = 0)
    (EL_a : ∀ t ∈ I,
      deriv (fun s => deriv (fun v => L 1 (a s) v (Φ s) (deriv Φ s) (h s) (f s)) (deriv a s)) t
        - deriv (fun u => L 1 u (deriv a t) (Φ t) (deriv Φ t) (h t) (f t)) (a t) = 0)
    (EL_Φ : ∀ t ∈ I,
      deriv (fun s => deriv (fun w => L 1 (a s) (deriv a s) (Φ s) w (h s) (f s)) (deriv Φ s)) t
        - deriv (fun u => L 1 (a t) (deriv a t) u (deriv Φ t) (h t) (f t)) (Φ t) = 0)
    (EL_h : ∀ t ∈ I,
      deriv (fun w => L 1 (a t) (deriv a t) (Φ t) (deriv Φ t) w (f t)) (h t) = 0)
    (EL_f : ∀ t ∈ I,
      deriv (fun w => L 1 (a t) (deriv a t) (Φ t) (deriv Φ t) (h t) w) (f t) = 0) :
    let H : ℝ → ℝ := fun t => deriv a t / a t
    ∀ t ∈ I,
      3 * H t ^ 2 = κ ^ 2 * (deriv Φ t ^ 2 / 2 + V (Φ t) + 3 / 8 * H t ^ 2 * Φ t ^ 2
          + 3 / 4 * H t * h t * Φ t ^ 2)
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * h t ^ 2
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * f t ^ 2 ∧
      -2 * deriv H t - 3 * H t ^ 2 = κ ^ 2 * (deriv Φ t ^ 2 / 2 - V (Φ t)
          - 3 / 8 * H t ^ 2 * Φ t ^ 2 - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * h t ^ 2
        - 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * f t ^ 2 ∧
      deriv (deriv Φ) t + 3 * H t * deriv Φ t + deriv V (Φ t)
        - 3 / 4 * ((H t + h t) ^ 2 - f t ^ 2) * Φ t = 0 ∧
      h t = -(1 / 8) * (κ ^ 2 * Φ t ^ 2 / (1 + κ ^ 2 * Φ t ^ 2 / 8)) * (deriv a t / a t) ∧
      f t = 0 := by
  sorry

end PereiraGuimaraesElko
