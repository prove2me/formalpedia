-- Prove2me | Theorems.Thm_Pendulum_motion_unique
-- name    : Pendulum.motion_unique
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T17:22:11.08332+00:00
-- url     : https://prove2.me/theorems/3be3dd3d-f8db-420e-841a-a02735683a4a
-- title:
--   A pendulum motion is determined by its initial angle and angular velocity
-- statement:
--   Two motions of the same pendulum that start with the same angle and the same angular velocity are
--   the same motion.
--
--   Let $g,\ell\in\mathbb R$, and let $(\theta_1,\omega_1,\alpha_1)$ and $(\theta_2,\omega_2,\alpha_2)$
--   both be motions of the pendulum, i.e. both satisfy $\theta_i'=\omega_i$, $\omega_i'=\alpha_i$ and
--   Eq. 1,
--
--   $$\alpha_i(t)=-\frac{g}{\ell}\sin\theta_i(t)\qquad(t\in\mathbb R,\ i=1,2).$$
--
--   If $\theta_1(0)=\theta_2(0)$ and $\omega_1(0)=\omega_2(0)$, then
--
--   $$\theta_1=\theta_2\quad\text{and}\quad\omega_1=\omega_2$$
--
--   as functions on $\mathbb R$.
--
--   This is the uniqueness half of the well-posedness of the model, and it is used repeatedly later:
--   it is what forbids a motion from reaching the upright position with zero angular velocity unless it
--   is the upright equilibrium itself, and it is what turns the reflection symmetry $t\mapsto-t$ of the
--   equation into a symmetry of a given motion.
--
--   **Formalization Note** Equality of the angular accelerations follows from the conclusion and Eq. 1,
--   so it is not stated separately.
-- source:
--   Wikipedia, Pendulum (mechanics), revision 1374595895, https://en.wikipedia.org/w/index.php?title=Pendulum_(mechanics)&oldid=1374595895

import Mathlib
import Definitions.Def_PendulumDefs

namespace Pendulum

theorem motion_unique (g l : ℝ) (theta₁ omega₁ alpha₁ theta₂ omega₂ alpha₂ : ℝ → ℝ)
    (h₁ : IsMotion g l theta₁ omega₁ alpha₁) (h₂ : IsMotion g l theta₂ omega₂ alpha₂)
    (hθ : theta₁ 0 = theta₂ 0) (hω : omega₁ 0 = omega₂ 0) :
    theta₁ = theta₂ ∧ omega₁ = omega₂ := by sorry

end Pendulum
