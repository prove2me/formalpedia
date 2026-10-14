-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_angle_from_cos_sin_estimates
-- name    : QAlgorithms.Nannicini.angle_from_cos_sin_estimates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:44:36.783072+00:00
-- url     : https://prove2.me/theorems/616cb4db-a23f-4f18-89e5-5149b1eb123a
-- title:
--   Combining cosine and sine estimates into an angle estimate (corrected)
-- statement:
--   There is a rule $F:\mathbb R^2\to\mathbb R$ turning estimates $\tilde c,\tilde s$ of the cosine and sine of an angle into an angle estimate $\tilde\varphi=F(\tilde c,\tilde s)$ with the following property. For every $0\le\eta<\pi/2$, every $\varphi\in[0,2\pi]$ and all reals $\tilde c,\tilde s$ with
--
--   $$
--   |\tilde c-\cos\varphi|\le\frac{\sin\eta}{\sqrt2},\qquad |\tilde s-\sin\varphi|\le\frac{\sin\eta}{\sqrt2},
--   $$
--
--   the estimate is within $\eta$ of $\varphi$ modulo $2\pi$:
--
--   $$
--   \operatorname{dist}_{2\pi}\big(F(\tilde c,\tilde s),\varphi\big)\le\eta,\qquad \operatorname{dist}_{2\pi}(x,y)=\min_{k\in\mathbb Z}|x-y-2\pi k| .
--   $$
--
--   This is the constant-precision step of iterative phase estimation: errors of $\sin\eta/\sqrt2$ in the sampled cosine and sine give an angle error of $\eta$.
--
--   **Formalization Note** The page states $\eta\le\pi/2$ and the plain distance $|\tilde\varphi-\varphi|$; read literally the statement is false ($\varphi=0$ and $\varphi=2\pi$ have the same exact estimates; at $\eta=\pi/2$ the estimates $(0,0)$ fit $\varphi=\pi/4,3\pi/4,5\pi/4,7\pi/4$). The corrected version uses the distance modulo $2\pi$ (angles are defined modulo $2\pi$, p.66) and $\eta<\pi/2$. The rule $F$ is chosen before $\eta$, $\varphi$ and the estimates, so it cannot depend on the true angle. The angular distance is written as $2\pi\cdot$`circDist`$(\tilde\varphi/2\pi,\varphi/2\pi)$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 66, Proposition 3.16. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms


/-- Nannicini p.66, Proposition 3.16 (combining sine and cosine estimates), **corrected**
(trap 30, see `HARD.md`): there is a rule `F` turning estimates `c̃, s̃` of `cos φ, sin φ` into an
angle estimate `φ̃ = F c̃ s̃` such that, for every `0 ≤ η < π/2` and `φ ∈ [0, 2π]`, the errors
`|c̃ − cos φ| ≤ sin η / √2` and `|s̃ − sin φ| ≤ sin η / √2` imply that `φ̃` is within `η` of `φ`
modulo `2π`. The page states `η ≤ π/2` and the plain distance `|φ̃ − φ|`; both readings are
false (at `η = π/2` the estimates `(0, 0)` fit `φ = π/4, 3π/4, 5π/4, 7π/4`; `φ = 0` and `φ = 2π`
have the same exact estimates), while angles are defined modulo `2π` (p.66). The angular
distance is `2π · circDist (φ̃ / 2π) (φ / 2π)`. -/
theorem angle_from_cos_sin_estimates :
    ∃ F : ℝ → ℝ → ℝ, ∀ η : ℝ, 0 ≤ η → η < Real.pi / 2 →
      ∀ φ : ℝ, 0 ≤ φ → φ ≤ 2 * Real.pi → ∀ c s : ℝ,
        |c - Real.cos φ| ≤ Real.sin η / Real.sqrt 2 →
        |s - Real.sin φ| ≤ Real.sin η / Real.sqrt 2 →
        2 * Real.pi * circDist (F c s / (2 * Real.pi)) (φ / (2 * Real.pi)) ≤ η := by sorry


end QAlgorithms.Nannicini
