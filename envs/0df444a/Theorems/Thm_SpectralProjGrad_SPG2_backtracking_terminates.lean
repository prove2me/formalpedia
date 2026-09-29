-- Prove2me | Theorems.Thm_SpectralProjGrad_SPG2_backtracking_terminates
-- name    : SpectralProjGrad.SPG2.backtracking_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:01:35.877305+00:00
-- url     : https://prove2.me/theorems/bc989260-8b7f-4873-a676-80629fd79f71
-- title:
--   Theorem 2.1 (first clause): SPG2 is well defined — the backtracking terminates
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be closed and convex, let $f$ have continuous partial derivatives on an open set $U\supseteq\Omega$, with gradient $g=\nabla f$, and let $P$ be the orthogonal projection onto $\Omega$. Fix parameters $0<\alpha_{\min}<\alpha_{\max}$, $\gamma\in(0,1)$ and $0<\sigma_1<\sigma_2<1$.
--
--   Let $x\in\Omega$ be a point at which Step 1 of SPG2 does not stop, i.e. $\|P(x-g(x))-x\|\ne0$; let $\alpha\in[\alpha_{\min},\alpha_{\max}]$ and $d=P(x-\alpha g(x))-x$; and let $R$ be any real number with $R\ge f(x)$. Then for every sequence of trial steps $(\mu_i)_{i\ge0}$ with $\mu_0=1$ and $\mu_{i+1}\in[\sigma_1\mu_i,\sigma_2\mu_i]$ there is an index $i$ with
--
--   $$
--   f(x+\mu_i d)\le R+\gamma\,\mu_i\,\langle d,g(x)\rangle .
--   $$
--
--   Applied at $x=x_k$, $\alpha=\alpha_k$ and $R=R_k=\max_{0\le j\le\min\{k,M-1\}}f(x_{k-j})$ (which satisfies $R_k\ge f(x_k)$, the term $j=0$), this is the statement that the backtracking loop of Step 2 of SPG2 terminates after finitely many trials, whatever choices rule (2) makes: Algorithm SPG2 is well defined.
--
--   **Formalization Note** The paper's clause "Algorithm SPG2 is well defined" is formalized in single-iteration form, for an arbitrary reference value $R\ge f(x)$; it implies the paper's clause at every iteration of every run.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 5, Theorem 2.1 (first clause), for Algorithm 2.2 Step 2 (p. 4) and Step 1 of Algorithm 2.1 (p. 3)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad

namespace SpectralProjGrad.SPG2

/-- Theorem 2.1, first clause (SPG2 is well defined), in single-iteration form: at a point
`x ∈ Ω` where Step 1 does not stop (`‖P(x - g(x)) - x‖ ≠ 0`), with `α ∈ [α_min, α_max]`,
`d = P(x - α g(x)) - x` and any reference value `R ≥ f(x)`, every backtracking sequence
`μ_0 = 1`, `μ_{i+1} ∈ [σ₁ μ_i, σ₂ μ_i]` reaches a trial step satisfying the nonmonotone
Armijo test `f(x + μ_i d) ≤ R + γ μ_i ⟨d, g(x)⟩`. -/
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
    (μ : ℕ → ℝ) (hμ0 : μ 0 = 1)
    (hμ : ∀ i, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) :
    ∃ i, f (x + μ i • SpectralProjGrad.Shared.scaledProjGrad P f α x) ≤
      R + γ * μ i * inner ℝ (SpectralProjGrad.Shared.scaledProjGrad P f α x) (gradient f x) := by sorry

end SpectralProjGrad.SPG2
