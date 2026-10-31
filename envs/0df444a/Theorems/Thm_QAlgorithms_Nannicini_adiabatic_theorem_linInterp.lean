-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_adiabatic_theorem_linInterp
-- name    : QAlgorithms.Nannicini.adiabatic_theorem_linInterp
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:53:45.966693+00:00
-- url     : https://prove2.me/theorems/52c41e17-38ac-4a3b-9387-3eb804659394
-- title:
--   Adiabatic theorem for the linear interpolation (1 − s)H_I + sH_F
-- statement:
--   There is an absolute constant $c$ with the following property.
--
--   Let $H_I, H_F$ be Hermitian matrices on a finite-dimensional space $\mathbb{C}^\iota$ and let
--
--   $$
--   H(s) = (1-s) H_I + s H_F, \qquad s \in [0,1],
--   $$
--
--   be their linear interpolation (Eq. (9.6)). Let $\lambda : [0,1] \to \mathbb{R}$ be continuous and let $|\varphi(s)\rangle$ be a unit eigenvector of $H(s)$ with eigenvalue $\lambda(s)$. Let $\gamma > 0$ be a spectral gap around $\lambda$: for every $s$, $\lambda(s)$ is a simple eigenvalue of $H(s)$ and every other eigenvalue lies at distance at least $\gamma$ from it. Let $\delta > 0$ and
--
--   $$
--   T \ge \frac{c}{\delta}\left(\frac{\|H_F - H_I\|}{\gamma^2} + \frac{\|H_F - H_I\|^2}{\gamma^3}\right).
--   $$
--
--   If $|\psi(s)\rangle$ solves $\frac{d|\psi(s)\rangle}{ds} = iT\,H(s)|\psi(s)\rangle$ on $[0,1]$ with $|\psi(0)\rangle = |\varphi(0)\rangle$, then
--
--   $$
--   \bigl\| e^{i\theta}|\psi(1)\rangle - |\varphi(1)\rangle \bigr\| \le \delta \quad \text{for some } \theta \in \mathbb{R}.
--   $$
--
--   This is the form of the adiabatic theorem used for adiabatic optimization by linear interpolation: the running time is governed by $\|H_F - H_I\|$ and the minimum gap $\gamma$ along the path.
--
--   **Formalization Note** $\|\cdot\|$ is the operator norm. Since $H' = H_F - H_I$ and $H'' = 0$, no derivative data are supplied. The source's $\gamma = \min_s \gamma(s)$ is replaced by any lower bound $\gamma > 0$ on the gaps, which is equivalent because the bound on $T$ decreases in $\gamma$. The constant $c$ is quantified before all data.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 225, Corollary 9.24. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

universe u

namespace QAlgorithms.Nannicini



/-- Nannicini p.225, Corollary 9.24 (Adiabatic theorem for linear interpolation). There exists
some constant `c` such that, when the Hamiltonian `H(s)` performs linear interpolation between an
initial and a final Hamiltonian, as in Eq. (9.6), the statement of Thm. 9.11 holds if we choose `T`
satisfying `T ≥ (c/δ)(‖H_F − H_I‖/γ² + ‖H_F − H_I‖²/γ³)`.

`H(s) = (1 − s)H_I + sH_F` is the frozen `linInterp HI HF s` (Eq. (9.6)), with `H_I, H_F`
Hermitian; it is smooth, `H′ = H_F − H_I`, `H″ = 0`, so no derivative data are supplied. The
constant `c` precedes everything it is uniform over (trap 8). The gap `γ` of Def. 9.9 enters as
any `γ > 0` with `HasGapAround (H s) (λ s) γ` for all `s`, equivalent by monotonicity; the norm is
the operator norm `specNorm`. The other hypotheses are Theorem 9.11's. -/
theorem adiabatic_theorem_linInterp :
    ∃ c : ℝ, ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (HI HF : Matrix ι ι ℂ),
      HI.IsHermitian → HF.IsHermitian →
      ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
      ∀ (φ : ℝ → EuclideanSpace ℂ ι),
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsState (φ s) ∧ act (linInterp HI HF s) (φ s) = (lam s : ℂ) • φ s) →
      ∀ (γ : ℝ), 0 < γ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (linInterp HI HF s) (lam s) γ) →
      ∀ (δ : ℝ), 0 < δ → ∀ (T : ℝ),
      c / δ * (specNorm (HF - HI) / γ ^ 2 + specNorm (HF - HI) ^ 2 / γ ^ 3) ≤ T →
      ∀ (ψ : ℝ → EuclideanSpace ℂ ι), SolvesAdiabaticPlus (linInterp HI HF) T ψ → ψ 0 = φ 0 →
      ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ := by
  sorry


end QAlgorithms.Nannicini
