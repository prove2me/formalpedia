-- Prove2me | Theorems.Thm_SDYM_generalized_chazy_of_darboux_halphen
-- name    : SDYM.generalized_chazy_of_darboux_halphen
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T02:49:18.522128+00:00
-- url     : https://prove2.me/theorems/c9039c47-783e-4be6-b913-0578dd314a5c
-- title:
--   The generalized Chazy equation (81) from the generalized Darboux–Halphen system with $\alpha=\beta=\gamma=2/n$
-- statement:
--   Ablowitz, Chakravarty and Halburd showed that for a solution of the generalized Darboux–Halphen system (52) with $\tau^2$ given in the closed form (56),
--
--   $$\tau^2 = \alpha^2(\omega_1-\omega_2)(\omega_3-\omega_1) + \beta^2(\omega_2-\omega_3)(\omega_1-\omega_2) + \gamma^2(\omega_3-\omega_1)(\omega_2-\omega_3),$$
--
--   the trace variable $y = -2(\omega_1+\omega_2+\omega_3)$ solves the generalized Chazy equation
--
--   $$\frac{d^3y}{dt^3} - 2y\frac{d^2y}{dt^2} + 3\left(\frac{dy}{dt}\right)^2 = \frac{4}{36-n^2}\left(6\frac{dy}{dt}-y^2\right)^2$$
--
--   precisely when either $\alpha = \beta = \gamma = 2/n$, or exactly one of $\alpha,\beta,\gamma$ equals $2/n$ and the other two equal $1/3$. This milestone is the first of those two cases: it fixes $\alpha = \beta = \gamma = 2/n$ and asserts the resulting generalized Chazy equation. The classical Chazy equation is the limit $n = \infty$.
--
--   The statement records the first two derivatives of $y$ in closed form. Writing $e_1, e_2, e_3$ for the elementary symmetric functions of the $\omega_j$ and $\tau^2 = \tfrac{4}{n^2}(3e_2-e_1^2)$, they are
--
--   $$\frac{dy}{dt} = 2e_2 - 6\tau^2,\qquad \frac{d^2y}{dt^2} = -12e_3 + \frac{4}{n^2}\left(-4e_1^3 + 108e_3\right).$$
--
--   **Conventions shared with the rest of the mission.** All functions are complex-valued functions of a complex variable; a system is required to hold only at the points of an arbitrary set $s \subseteq \mathbb{C}$, with no openness, connectedness or holomorphy assumed; and each derivative that a statement mentions is carried by an explicit companion function tied to it by a pointwise differentiability assertion, so no statement ever refers to the value of a derivative that does not exist.
-- source:
--   M. J. Ablowitz, S. Chakravarty, R. G. Halburd, "Integrable systems and reductions of the self-dual Yang-Mills equations", J. Math. Phys. 44 (2003) 3147-3173, https://doi.org/10.1063/1.1586967, Sec. V.B p. 3170, Eqs. (80)-(81) together with Eq. (56) on p. 3165; this item covers the case α = β = γ = 2/n of the stated criterion

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

namespace SDYM

theorem generalized_chazy_of_darboux_halphen
    (n : ℂ) (hn : n ≠ 0) (hn36 : n ^ 2 ≠ 36) (s : Set ℂ) (w₁ w₂ w₃ : ℂ → ℂ)
    (h₁ : ∀ t ∈ s, HasDerivAt w₁ (w₂ t * w₃ t - w₁ t * (w₂ t + w₃ t)
      + (2 / n) ^ 2 * ((w₁ t - w₂ t) * (w₃ t - w₁ t) + (w₂ t - w₃ t) * (w₁ t - w₂ t)
        + (w₃ t - w₁ t) * (w₂ t - w₃ t))) t)
    (h₂ : ∀ t ∈ s, HasDerivAt w₂ (w₃ t * w₁ t - w₂ t * (w₃ t + w₁ t)
      + (2 / n) ^ 2 * ((w₁ t - w₂ t) * (w₃ t - w₁ t) + (w₂ t - w₃ t) * (w₁ t - w₂ t)
        + (w₃ t - w₁ t) * (w₂ t - w₃ t))) t)
    (h₃ : ∀ t ∈ s, HasDerivAt w₃ (w₁ t * w₂ t - w₃ t * (w₁ t + w₂ t)
      + (2 / n) ^ 2 * ((w₁ t - w₂ t) * (w₃ t - w₁ t) + (w₂ t - w₃ t) * (w₁ t - w₂ t)
        + (w₃ t - w₁ t) * (w₂ t - w₃ t))) t) :
    IsGeneralizedChazySolution n s
      (fun t => -2 * (w₁ t + w₂ t + w₃ t))
      (fun t => 2 * (w₁ t * w₂ t + w₂ t * w₃ t + w₃ t * w₁ t)
        - 6 * (4 / n ^ 2 * (3 * (w₁ t * w₂ t + w₂ t * w₃ t + w₃ t * w₁ t)
          - (w₁ t + w₂ t + w₃ t) ^ 2)))
      (fun t => -12 * (w₁ t * w₂ t * w₃ t)
        + 4 / n ^ 2 * (-4 * (w₁ t + w₂ t + w₃ t) ^ 3
          + 108 * (w₁ t * w₂ t * w₃ t))) := by sorry

end SDYM
