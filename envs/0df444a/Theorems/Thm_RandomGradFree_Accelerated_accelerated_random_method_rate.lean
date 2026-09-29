-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_accelerated_random_method_rate
-- name    : RandomGradFree.Accelerated.accelerated_random_method_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:10:24.404436+00:00
-- url     : https://prove2.me/theorems/9ba4fdc1-ad80-4ed9-a3f6-0cf6b947d047
-- title:
--   Theorem 9 — rate of the accelerated random method $\mathcal{FG}_\mu$ (Eq. (62)) — goal theorem
-- statement:
--   Let $E$ be a real inner product space of dimension $n \ge 2$. Let $f : E \to \mathbb R$ be differentiable with $L_1$-Lipschitz gradient, $L_1 > 0$, and strongly convex with parameter $\tau \ge 0$:
--
--   $$
--   f(y) \ge f(x) + \langle \nabla f(x), y - x\rangle + \frac{\tau}{2}\|y-x\|^2, \qquad x, y \in E
--   $$
--
--   ($\tau = 0$ is allowed and means $f$ is convex). Let $x^*$ be a minimizer of $f$, and write $f^* = f(x^*)$ and $\kappa = \tau/L_1$. Let $\mu \ge 0$, and set
--
--   $$
--   \theta_n = \frac{1}{16(n+4)^2L_1}, \qquad h_n = \frac{1}{4(n+4)L_1}.
--   $$
--
--   Consider a run of the accelerated random method $\mathcal{FG}_\mu$ (Eq. (60)) with these $\theta_n, h_n$, starting point $x_0$, sequences $(\gamma_k), (\alpha_k)$ with $\gamma_0 > 0$, $\gamma_0 \ge \tau$, and i.i.d. standard Gaussian directions. Let $\phi_k = \mathbb E f(x_k)$, and let $\psi_k = \prod_{i=0}^{k-1}(1-\alpha_i)$ and $C_k$ ($C_0 = 0$, $C_k = 1 + \sum_{i=1}^{k-1}\prod_{j=k-i}^{k-1}(1-\alpha_j)$) be as in the proof. Then for every $k \ge 0$,
--
--   $$
--   \phi_k - f^* \le \psi_k\Big[f(x_0) - f(x^*) + \frac{\gamma_0}{2}\|x_0 - x^*\|^2\Big] + \mu^2 L_1\Big(n + \frac{3(n+8)}{16}C_k\Big),
--   $$
--
--   where
--
--   1. $\psi_k \le \big(1 - \frac{\kappa^{1/2}}{4(n+4)}\big)^k$;
--   2. $\psi_k \le \big(1 + \frac{k}{8(n+4)}\sqrt{\gamma_0/L_1}\big)^{-2}$;
--   3. $C_k \le k$;
--   4. if $\tau > 0$, then $C_k \le \frac{4(n+4)}{\kappa^{1/2}}$.
--
--   With $\mu$ small this gives the $O(n^2/k^2)$ rate of an accelerated method that uses only function values, and linear convergence with ratio $1 - \kappa^{1/2}/(4(n+4))$ in the strongly convex case.
--
--   **Formalization Note** The paper prints $\theta_n = 1/(16(n+1)^2L_1(f))$. This statement uses $\theta_n = 1/(16(n+4)^2L_1(f))$: the proof (pp. 549–550) needs $h_n/(4(n+4)) - h_n^2L_1/2 = \theta_n/2$, $[\tau\theta_n]^{1/2} = \kappa^{1/2}/(4(n+4))$ and $\theta_n^{1/2} = 1/(4(n+4)L_1^{1/2})$, all of which hold only with $(n+4)$; with the printed value the first step of the proof fails. The paper's $\min\{\cdot,\cdot\}$ bounds are stated as separate conjuncts; the bound $C_k \le 4(n+4)/\kappa^{1/2}$ is guarded by $\tau > 0$ because at $\tau = 0$ the paper's value is $+\infty$. Convexity, solvability and $\dim E \ge 2$ are the standing assumptions of problem (53) in Section 5. The oracle at $\mu = 0$ is the limiting oracle $g_0$. $\phi_k$ is the Bochner integral of $f(x_k)$; under the hypotheses it is integrable.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 549, Theorem 9, Eq. (62) (with ψ_k, C_k from p. 550 and method (60), parameters θ_n, h_n from p. 548; problem (53) pp. 545-546)

import Mathlib
import Definitions.Def_RandomGradFree_Accelerated_psi
import Definitions.Def_RandomGradFree_Accelerated_C
import Definitions.Def_RandomGradFree_Accelerated_IsAcceleratedRandomRun

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem accelerated_random_method_rate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 < L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hsc : ∀ x y, f y ≥ f x + inner ℝ (gradient f x) (y - x) + τ / 2 * ‖y - x‖ ^ 2)
    (xstar : E) (hopt : ∀ y, f xstar ≤ f y)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (θ : ℝ) (hθ : θ = 1 / (16 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 * L₁))
    (h : ℝ) (hh : h = 1 / (4 * ((Module.finrank ℝ E : ℝ) + 4) * L₁))
    (x₀ : E) (γ α : ℕ → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u x v : ℕ → Ω → E) (hrun : IsAcceleratedRandomRun P f μ τ θ h x₀ γ α u x v) (k : ℕ) :
    (∫ ω, f (x k ω) ∂P) - f xstar
        ≤ psi α k * (f x₀ - f xstar + γ 0 / 2 * ‖x₀ - xstar‖ ^ 2)
          + μ ^ 2 * L₁ * ((Module.finrank ℝ E : ℝ)
            + 3 * ((Module.finrank ℝ E : ℝ) + 8) / 16 * C α k) ∧
      psi α k ≤ (1 - Real.sqrt (τ / L₁) / (4 * ((Module.finrank ℝ E : ℝ) + 4))) ^ k ∧
      psi α k ≤ 1 / (1 + k / (8 * ((Module.finrank ℝ E : ℝ) + 4)) * Real.sqrt (γ 0 / L₁)) ^ 2 ∧
      C α k ≤ k ∧
      (0 < τ → C α k ≤ 4 * ((Module.finrank ℝ E : ℝ) + 4) / Real.sqrt (τ / L₁)) := by sorry

end RandomGradFree.Accelerated
