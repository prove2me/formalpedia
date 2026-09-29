-- Prove2me | Theorems.Thm_SpectralProjGrad_SPG1_backtracking_terminates
-- name    : SpectralProjGrad.SPG1.backtracking_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:52:11.866112+00:00
-- url     : https://prove2.me/theorems/9f7d89e5-58ac-438c-a3df-ba4c24604b69
-- title:
--   Theorem 2.2 (first clause): SPG1 is well defined
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be closed and convex, let $f$ have continuous partial derivatives on an open set $U\supseteq\Omega$, with gradient $g=\nabla f$, and let $P$ be the orthogonal projection onto $\Omega$. Let $0<\alpha_{\min}<\alpha_{\max}$, $\gamma\in(0,1)$ and $0<\sigma_1<\sigma_2<1$.
--
--   Let $x\in\Omega$ be a point at which Step 1 of SPG1 does not stop, i.e. $\|P(x-g(x))-x\|\neq0$; let $\alpha\in[\alpha_{\min},\alpha_{\max}]$; and let $R$ be any real number with $R\ge f(x)$. Let $(\mu_i)_{i\ge0}$ be any sequence of trial steps with $\mu_0=\alpha$ and $\mu_{i+1}\in[\sigma_1\mu_i,\sigma_2\mu_i]$ for all $i$. Then some trial point $x_+=P(x-\mu_i\,g(x))$ satisfies
--
--   $$
--   f(x_+)\le R+\gamma\,\langle x_+-x,\,g(x)\rangle .
--   $$
--
--   Hence the backtracking loop of Step 2 of SPG1 always terminates after finitely many trials, whatever admissible choices are made in (2), so each iteration of the algorithm is well defined.
--
--   **Formalization Note** The statement is for a single iteration. The reference value $R$ stands for the paper's $\max_{0\le j\le\min\{k,M-1\}} f(x_{k-j})$, which is at least $f(x_k)$ because $j=0$ is in the range; stating it for every $R\ge f(x)$ covers every iteration of every run. The remaining parts of the iteration (Step 3, and $x_{k+1}\in\Omega$) are explicit formulas and need no statement.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 5, Theorem 2.2 (first clause: Algorithm SPG1 is well defined)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto

namespace SpectralProjGrad.SPG1

/-- Theorem 2.2, first clause (SPG1 is well defined), in single-iteration form: at a point
`x ∈ Ω` where Step 1 does not stop (`‖P(x - g(x)) - x‖ ≠ 0`), with `α ∈ [α_min, α_max]` and any
reference value `R ≥ f(x)`, every backtracking sequence `μ_0 = α`, `μ_{i+1} ∈ [σ₁ μ_i, σ₂ μ_i]`
reaches a trial point `x₊ = P(x - μ_i g(x))` satisfying the nonmonotone Armijo test (1)
along the projection arc: `f(x₊) ≤ R + γ ⟨x₊ - x, g(x)⟩`. -/
theorem backtracking_terminates {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {αmin αmax γ σ₁ σ₂ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (hγ : γ ∈ Set.Ioo 0 1) (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) (hσ₂ : σ₂ < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (hstep1 : ‖P (x - gradient f x) - x‖ ≠ 0)
    (α : ℝ) (hα : α ∈ Set.Icc αmin αmax)
    (R : ℝ) (hR : f x ≤ R)
    (μ : ℕ → ℝ) (hμ0 : μ 0 = α)
    (hμ : ∀ i, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) :
    ∃ i, f (P (x - μ i • gradient f x)) ≤
      R + γ * inner ℝ (P (x - μ i • gradient f x) - x) (gradient f x) := by sorry

end SpectralProjGrad.SPG1
