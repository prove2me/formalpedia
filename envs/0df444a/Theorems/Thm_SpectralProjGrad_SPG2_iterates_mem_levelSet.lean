-- Prove2me | Theorems.Thm_SpectralProjGrad_SPG2_iterates_mem_levelSet
-- name    : SpectralProjGrad.SPG2.iterates_mem_levelSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:02:24.006987+00:00
-- url     : https://prove2.me/theorems/0c61d939-a8a3-4e27-911f-ced550def5b7
-- title:
--   SPG2 iterates stay in the level set $\Omega_0=\{x\in\Omega: f(x)\le f(x_0)\}$
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be closed and convex, let $f$ have continuous partial derivatives on an open set $U\supseteq\Omega$, with gradient $g=\nabla f$, and let $P$ be the orthogonal projection onto $\Omega$. Fix parameters $M\ge1$, $0<\alpha_{\min}<\alpha_{\max}$, $\gamma\in(0,1)$ and $0<\sigma_1<\sigma_2<1$. For every infinite run $(x_k,\alpha_k)$ of Algorithm SPG2 and every $k\ge0$,
--
--   $$
--   x_k\in\Omega_0\equiv\{x\in\Omega:\ f(x)\le f(x_0)\}.
--   $$
--
--   The nonmonotone line search allows $f(x_{k+1})>f(x_k)$, but never an increase above the starting value; this confines the whole sequence, and in particular all its accumulation points, to the level set $\Omega_0$.
--
--   **Formalization Note** "The sequence $\{x_k\}$" is the sequence of an infinite run (`IsSPG2Run`), i.e. one on which Step 1 never stops.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 4, Section 2, remark after Algorithm 2.2 (unnumbered)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_SPG2_IsSPG2Run

namespace SpectralProjGrad.SPG2

/-- Section 2, p. 4: the line search condition (3) guarantees that the SPG2 iterates remain in
`Ω₀ = {x ∈ Ω : f(x) ≤ f(x₀)}`. -/
theorem iterates_mem_levelSet {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {M : ℕ} {αmin αmax γ σ₁ σ₂ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hM : 1 ≤ M) (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (hγ : γ ∈ Set.Ioo 0 1) (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) (hσ₂ : σ₂ < 1)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {α : ℕ → ℝ}
    (hrun : IsSPG2Run Ω f P M αmin αmax γ σ₁ σ₂ x α) :
    ∀ k, x k ∈ {y ∈ Ω | f y ≤ f (x 0)} := by sorry

end SpectralProjGrad.SPG2
