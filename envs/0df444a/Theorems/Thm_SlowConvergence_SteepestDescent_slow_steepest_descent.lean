-- Prove2me | Theorems.Thm_SlowConvergence_SteepestDescent_slow_steepest_descent
-- name    : SlowConvergence.SteepestDescent.slow_steepest_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:31.200256+00:00
-- url     : https://prove2.me/theorems/b01358bc-3770-4da4-b0a5-4f161a5356f5
-- title:
--   Steepest descent can need $\lfloor \epsilon^{-(2-\tau)} \rfloor$ iterates to reach $|g| \le \epsilon$ (§2, p. 5; §6, p. 15)
-- statement:
--   Let $0 < \tau < 1$, let $0 < \underline\alpha \le \overline\alpha < 2$, and let $(\alpha_k)_{k\ge0}$ be any sequence of step lengths with $\underline\alpha \le \alpha_k \le \overline\alpha$ for all $k$ (condition (2.6)). Then there is a function $f : \mathbb R \to \mathbb R$ such that
--
--   1. $f$ is twice continuously differentiable and bounded below, and its derivative $f'$ is bounded and Lipschitz continuous (assumption AS.0);
--   2. the steepest descent method with these step lengths, $x_0 = 0$ and $x_{k+1} = x_k - \alpha_k f'(x_k)$, produces gradients
--   $$|f'(x_k)| = \Big(\frac{1}{k+1}\Big)^{\frac{1}{2-\tau}} \qquad \text{for every } k \ge 0;$$
--   3. consequently, for every $\epsilon \in (0,1)$, any iterate with $|f'(x_k)| \le \epsilon$ has
--   $$k + 1 \ge \Big\lfloor \frac{1}{\epsilon^{2-\tau}} \Big\rfloor .$$
--
--   In the paper's words: for any $\tau > 0$, steepest descent (with a Goldstein–Armijo linesearch) may require at least $\lfloor 1/\epsilon^{2-\tau} \rfloor$ iterations and function evaluations to produce an iterate with $\|g_k\| \le \epsilon$. Since $\tau$ is arbitrary, the known $O(\epsilon^{-2})$ upper bound for steepest descent is essentially sharp.
--
--   **Formalization Note** The theorem is stated for $\tau \in (0,1)$, which the construction needs; for $\epsilon < 1$ a smaller $\tau$ gives a larger count, so this covers every $\tau > 0$. The count is $k + 1$, the number of iterates $x_0,\dots,x_k$ (function evaluations): as printed, "at least $\lfloor 1/\epsilon^{2-\tau}\rfloor$ iterations" is off by one, since with $\epsilon = N^{-1/(2-\tau)}$ the iterate $x_{N-1}$ already reaches $|g| = \epsilon$. The function $f$ is required on all of $\mathbb R$ with every property global; the paper builds it on $[0,\infty)$ and notes that it extends smoothly to the negative reals. The step lengths are quantified first, so $f$ may depend on them, as in the paper; the method's run is part of the conclusion and is tied to $f$ through $x_{k+1} = x_k - \alpha_k f'(x_k)$.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 5, §2, final paragraph; p. 15, §6, first paragraph; p. 3, AS.0 and (2.6)

import Mathlib

namespace SlowConvergence.SteepestDescent

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §2, final paragraph, p. 5 (restated in §6, p. 15):
"for any τ > 0, the steepest descent method (with a Goldstein-Armijo linesearch) may require, for any
ϵ ∈ (0, 1), at least ⌊1/ϵ^{2−τ}⌋ iterations for producing an iterate x_k such that ∥g_k∥ ≤ ϵ."

For every `τ ∈ (0, 1)`, all step-length bounds `0 < α̲ ≤ ᾱ < 2` (2.6) and every step-length sequence
`α_k ∈ [α̲, ᾱ]`, there is a twice continuously differentiable `f : ℝ → ℝ`, bounded below, with bounded
and Lipschitz continuous derivative (AS.0, p. 3), on which steepest descent `x_{k+1} = x_k − α_k f'(x_k)`
from `x_0 = 0` produces `|f'(x_k)| = (1/(k+1))^{1/(2−τ)}` for every `k`, so that an iterate with
`|f'(x_k)| ≤ ε < 1` needs `k + 1 ≥ ⌊ε^{−(2−τ)}⌋` iterates `x_0, …, x_k`.

Formalization Notes: `τ < 1` is imposed (the construction needs `1/(2−τ) < 1`; for `ε < 1` smaller `τ`
gives larger counts, so this covers every `τ > 0`). The count is stated for `k + 1`, the number of
iterates `x_0, …, x_k`; the printed count of iterations `k` is off by one. -/
theorem slow_steepest_descent (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (αlo αhi : ℝ) (hlo : 0 < αlo) (hlohi : αlo ≤ αhi) (hhi : αhi < 2)
    (α : ℕ → ℝ) (hα : ∀ k, αlo ≤ α k ∧ α k ≤ αhi) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧ (∃ M : ℝ, ∀ x, |deriv f x| ≤ M) ∧
      (∃ L : NNReal, LipschitzWith L (deriv f)) ∧
      ∃ x : ℕ → ℝ, x 0 = 0 ∧ (∀ k : ℕ, x (k + 1) = x k - α k * deriv f (x k)) ∧
        (∀ k : ℕ, |deriv f (x k)| = (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ))) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ, |deriv f (x k)| ≤ ε →
          (⌊ε ^ (-(2 - τ))⌋₊ : ℝ) ≤ (k : ℝ) + 1) := by sorry

end SlowConvergence.SteepestDescent
