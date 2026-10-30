-- Prove2me | Theorems.Thm_StaggeredRollout_TOpt_omega_star_minimizes_f1
-- name    : StaggeredRollout.TOpt.omega_star_minimizes_f1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T04:00:21.278301+00:00
-- url     : https://prove2.me/theorems/51fab7f0-e6ec-4049-bd53-29befa289110
-- title:
--   Proof of Theorem 3.1, p. ec25 (corrected: (EC.2.6) linear term over t = j, …, j_ℓ with b_{ℓ,t} = (T_ℓ+1−2t)/T_ℓ) — ω* minimizes f₁ over nondecreasing ω ∈ [−1, 1]^T
-- statement:
--   **$\omega^*$ solves the relaxed fraction problem** (proof of Theorem 3.1, p. ec25).
--
--   Let $\ell\ge0$, and if $\ell>0$ let $T>(\ell^3+13\ell^2+7\ell+3)/(8\ell)$. For a path $\omega\in\mathbb R^T$ let
--   $$
--   f_1(\omega)=\sum_{j=1}^{\ell+1}\Big[\sum_{t=j}^{T-\ell-1+j}\omega_t^2-\frac1{T-\ell}\Big(\sum_{t=j}^{T-\ell-1+j}\omega_t\Big)^2+\sum_{t=j}^{T-\ell-1+j}\frac{2(T-\ell-1+2j-2t)}{T-\ell}\,\omega_t\Big],
--   $$
--   which is $\sum_j f_{j,1}(\omega)$ with the corrected $b_\ell$. Then the S-shaped path $\omega^*_\ell$ of (3.4) is feasible for the relaxed problem
--   $$
--   \min\ f_1(\omega)\quad\text{s.t.}\quad -1\le\omega_t\le1,\ \ \omega_t\le\omega_{t+1},
--   $$
--   and minimizes it: $f_1(\omega^*_\ell)\le f_1(\omega)$ for every nondecreasing $\omega\in[-1,1]^T$.
--
--   Since $f_{j,1}$ depends on a design only through its treated fractions, and every staggered design has a nondecreasing fraction path in $[-1,1]$, this is the step of Theorem 3.1 that identifies the optimal fractions $(1+\omega^*_{\ell,t})/2$.
--
--   **Formalization Note** $\omega$ is a function `Fin T → ℝ` (0-based periods); "nondecreasing" is `Monotone`. Feasibility of $\omega^*$ is stated as part of "optimal solution".
--
--   Differences from the source:
--   - correction: (EC.2.6): linear term Σ_{t=1}^{T−ℓ−1+j} 2(T−ℓ−1+2j−2t)/(T−ℓ) ω_t, and f_{j,1} with b_{ℓ,t} = (T_ℓ+2−2t)/T_ℓ in (EC.1.7) → f1 = Σ_j f1j with linear term 2 b_ℓ⊤ω_{j:j_ℓ} over the window t = j, …, j_ℓ and b_{ℓ,t} = (T_ℓ+1−2t)/T_ℓ; reason: with the printed sum from t = 1, ω* is not a minimizer: ℓ = 2, T = 6 (threshold 77/16) gives −11.446 at ω* and about −12.089 at the feasible ω ≈ (−1, −1, −0.393, 0.107, 0.571, 1); the window form is the one of the display closing the proof of Lemma EC.1.2 (p. ec20), and the printed b_ℓ is false by the counterexample in Lemma EC.1.2
--   - reading: 'the ω* defined in Equation (3.5)' → omegaStar ℓ T, the ω* of (3.4); reason: (3.5) is the definition of 𝔸_opt; ω* is defined in (3.4)
--   - reading: 'ω* is an optimal solution that minimizes f_{j,1}(Z)' over the constraints −1 ≤ ω_t ≤ 1, ω_t ≤ ω_{t+1} of the Lagrangian (p. ec21) → Monotone ω* ∧ −1 ≤ ω* ≤ 1 ∧ ∀ ω monotone with values in [−1, 1], f1 ω* ≤ f1 ω; reason: an optimal solution is feasible and attains the minimum; the minimized function is the sum over j, as in (EC.2.6)
--   - reading: T > (ℓ³ + 13ℓ² + 7ℓ + 3)/(8ℓ) → 0 < ℓ → (ℓ³ + 13ℓ² + 7ℓ + 3)/(8ℓ) < T; reason: the expression is undefined at ℓ = 0, where Example 3.2 gives ω* for every T and the proof needs no condition
--   - encoding: periods 1, …, T and adoption time ∞ → Fin T (0-based: period t is index t − 1) and ⊤ of WithTop (Fin T); reason: Lean convention; same instances, and ⊤ keeps 'larger = later' (footnote 6)
-- source:
--   Xiong, Athey, Bayati, Imbens, Optimal Experimental Design for Staggered Rollouts, arXiv:1911.03764v6, p. ec25 (PDF 61), proof of Theorem 3.1, end of Case 3; feasible set from the Lagrangian on p. ec21, (EC.2.6)

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Setting
import Definitions.Def_StaggeredRollout_TOpt_Quadratic

namespace StaggeredRollout.TOpt
open Matrix

theorem omega_star_minimizes_f1 (ℓ T : ℕ)
    (hT : 0 < ℓ → ((ℓ : ℝ) ^ 3 + 13 * (ℓ : ℝ) ^ 2 + 7 * (ℓ : ℝ) + 3) / (8 * (ℓ : ℝ)) < (T : ℝ)) :
    Monotone (omegaStar ℓ T) ∧ (∀ t, -1 ≤ omegaStar ℓ T t ∧ omegaStar ℓ T t ≤ 1) ∧
    ∀ ω : Fin T → ℝ, Monotone ω → (∀ t, -1 ≤ ω t ∧ ω t ≤ 1) →
      f1 ℓ T (omegaStar ℓ T) ≤ f1 ℓ T ω := by sorry

end StaggeredRollout.TOpt
