-- Prove2me | Theorems.Thm_SlowConvergence_ARC_slow_arc
-- name    : SlowConvergence.ARC.slow_arc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:05.116574+00:00
-- url     : https://prove2.me/theorems/1d873180-f7c1-47d1-b494-30e911d7f755
-- title:
--   ARC can need $\lfloor\epsilon^{-(3/2-\tau)}\rfloor$ iterations to reach $|g|\le\epsilon$ (§5, pp. 13–15; §6, p. 16)
-- statement:
--   For a twice differentiable $f:\mathbb R\to\mathbb R$, the Adaptive Regularization with Cubics (ARC) algorithm computes, at each iterate $x_k$, a global minimizer $s_k$ of the cubic model
--   $$m_k(x_k+s) = f(x_k) + f'(x_k)s + \tfrac12 f''(x_k)s^2 + \tfrac13\sigma_k|s|^3,$$
--   accepts $x_{k+1} = x_k + s_k$ when the ratio $\rho_k$ of achieved to predicted decrease is at least $\eta_1$, and updates the weight $\sigma_k$ according to $\rho_k$, with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$.
--
--   **Theorem.** For every $\tau\in(0,1)$ there is a function $f:\mathbb R\to\mathbb R$ such that
--
--   1. $f$ is twice continuously differentiable and bounded below, $f''$ is bounded, and $f''$ is Lipschitz continuous on $\mathbb R$;
--   2. there are iterates $x_k$ with $x_0 = 0$, steps $s_k$ and weights $\sigma_k$ with $\sigma_0 = 1$ that form a run of ARC on $f$ for **every** admissible choice of $\gamma_1,\gamma_2,\eta_1,\eta_2$, every iteration being very successful ($\rho_k > \eta_2$);
--   3. the gradients along the run satisfy (5.1),
--   $$|f'(x_k)| = \Big(\frac1{k+1}\Big)^{\frac2{3-2\tau}}\qquad(k\ge0);$$
--   4. consequently, for every $\epsilon\in(0,1)$, if $|f'(x_k)|\le\epsilon$ then
--   $$k+1 \ \ge\ \Big\lfloor \frac1{\epsilon^{3/2-\tau}}\Big\rfloor ,$$
--   that is, at least $\lfloor\epsilon^{-(3/2-\tau)}\rfloor$ iterates (function evaluations) $x_0,\dots,x_k$ are needed.
--
--   Since ARC needs at most $O(\epsilon^{-3/2})$ iterations on such functions, this shows that the exponent $3/2$ cannot be lowered.
--
--   **Formalization Note** The paper says "for any $\tau>0$"; the construction needs $\tau<1$, and for $\epsilon<1$ the $\tau<1$ cases imply the bound for every $\tau>0$. The count is $k+1$ (iterates $x_0,\dots,x_k$): the printed "at least $\lfloor1/\epsilon^{3/2-\tau}\rfloor$ iterations" is off by one, and $\le k$ would be false. The paper builds $f$ on $[0,\infty)$ and says it extends smoothly to the negative reals; here $f$ is required on all of $\mathbb R$, with a globally Lipschitz second derivative. The ARC acceptance and update rules are those of Algorithm 2.1 of Cartis, Gould and Toint (2009a), cited on p. 2; the step is an exact global model minimizer with the exact second derivative. The function and the run are existentially quantified; the explicit construction is in the milestones.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, pp. 13–15, §5 (the f_4 example) and p. 16, §6

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Method

namespace SlowConvergence.ARC

/-- Cartis, Gould & Toint, *On the complexity of steepest descent, Newton's and regularized Newton's
methods for nonconvex unconstrained optimization*, preprint 15 Oct 2009, §5, pp. 13–15 (the `f_4`
example) and §6, p. 16: the ARC algorithm can need `⌊ε^{−(3/2−τ)}⌋` iterations to reach `|g| ≤ ε`.

For every `τ ∈ (0, 1)` there is a function `f : ℝ → ℝ` that is twice continuously differentiable,
bounded below, with bounded second derivative and globally Lipschitz continuous second derivative,
and sequences of iterates `x_k` (with `x_0 = 0`), steps `s_k` and weights `σ_k` (with `σ_0 = 1`) that
form a run of ARC on `f` for every admissible choice of the parameters `γ₂ ≥ γ₁ > 1`, `1 > η₂ ≥ η₁ > 0`,
every iteration being very successful (`ρ_k > η₂`), such that
* (5.1) `|f'(x_k)| = (1/(k+1))^{2/(3−2τ)}` for all `k ≥ 0`;
* for every `ε ∈ (0, 1)`, an iterate `x_k` with `|f'(x_k)| ≤ ε` has `k + 1 ≥ ⌊ε^{−(3/2−τ)}⌋`, i.e. at least
  `⌊1/ε^{3/2−τ}⌋` iterates (function evaluations) `x_0, …, x_k` are needed.

Formalization Note: the paper says "for any τ > 0"; the construction needs `τ < 1`, and the `τ < 1` cases
imply the iteration bound for all `τ > 0` when `ε < 1`. The count is `k + 1` (iterates `x_0, …, x_k`),
because as printed ("at least ⌊1/ε^{3/2−τ}⌋ iterations") it is off by one. The paper builds `f` on
`[0, ∞)` and says it extends smoothly; here `f` is required on all of `ℝ`. The ARC rules are those of
Algorithm 2.1 of Cartis, Gould and Toint (2009a), with the step an exact global model minimizer. -/
theorem slow_arc (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧
      (∃ M : ℝ, ∀ y, |deriv (deriv f) y| ≤ M) ∧
      (∃ L : NNReal, LipschitzWith L (deriv (deriv f))) ∧
      ∃ x s σ : ℕ → ℝ, x 0 = 0 ∧ σ 0 = 1 ∧
        (∀ γ₁ γ₂ η₁ η₂ : ℝ, 1 < γ₁ → γ₁ ≤ γ₂ → 0 < η₁ → η₁ ≤ η₂ → η₂ < 1 →
          IsARCRun f γ₁ γ₂ η₁ η₂ x s σ ∧ ∀ k, η₂ < rho f (σ k) (x k) (s k)) ∧
        (∀ k : ℕ, |deriv f (x k)| = (1 / ((k : ℝ) + 1)) ^ (2 / (3 - 2 * τ))) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ, |deriv f (x k)| ≤ ε →
          (⌊ε ^ (-(3 / 2 - τ))⌋₊ : ℝ) ≤ k + 1) := by sorry

end SlowConvergence.ARC
