-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_adiabatic_theorem_integral_gap
-- name    : QAlgorithms.Nannicini.adiabatic_theorem_integral_gap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:51:26.024212+00:00
-- url     : https://prove2.me/theorems/ffed5e5a-a4de-4d39-9643-8328f870ab63
-- title:
--   Adiabatic theorem with the integrated 1/γ³ gap dependence
-- statement:
--   There is an absolute constant $c$ with the following property.
--
--   Let $H(s)$, $s \in [0,1]$, be a time-dependent Hamiltonian on a finite-dimensional space $\mathbb{C}^\iota$: each $H(s)$ is Hermitian, and the entries of $H$ are twice differentiable on $[0,1]$ with entrywise derivatives $H'(s), H''(s)$. Let $\lambda : [0,1] \to \mathbb{R}$ be continuous and let $|\varphi(s)\rangle$ be a unit eigenvector of $H(s)$ with eigenvalue $\lambda(s)$. Let $g : [0,1] \to \mathbb{R}$ be a lower bound on the instantaneous spectral gap around $\lambda$: for every $s$, $\lambda(s)$ is a simple eigenvalue of $H(s)$ and every other eigenvalue lies at distance at least $g(s)$ from it. Assume $g(s) \ge \gamma_0$ for all $s$, for some $\gamma_0 > 0$, and that $s \mapsto \|H'(s)\|^2/g(s)^3 + \|H''(s)\|/g(s)^2$ is integrable on $[0,1]$. Let $\delta > 0$ and
--
--   $$
--   T \ge \frac{c}{\delta}\left(\frac{\|H'(0)\|}{g(0)^2} + \frac{\|H'(1)\|}{g(1)^2} + \int_0^1 \left(\frac{\|H'(s)\|^2}{g(s)^3} + \frac{\|H''(s)\|}{g(s)^2}\right) ds\right).
--   $$
--
--   If $|\psi(s)\rangle$ solves $\frac{d|\psi(s)\rangle}{ds} = iT\,H(s)|\psi(s)\rangle$ on $[0,1]$ with $|\psi(0)\rangle = |\varphi(0)\rangle$, then
--
--   $$
--   \bigl\| e^{i\theta}|\psi(1)\rangle - |\varphi(1)\rangle \bigr\| \le \delta \quad \text{for some } \theta \in \mathbb{R}.
--   $$
--
--   Compared with Theorem 9.11, the dependence on the gap improves from $1/\gamma^4$ to $1/\gamma^3$, the gap enters pointwise through an integral, and the accuracy enters as $1/\delta$ instead of $1/\delta^2$.
--
--   **Formalization Note** Norms are operator norms, and derivatives at $s = 0, 1$ are one-sided. The source's instantaneous gap $\gamma(s)$ (Def. 9.8) is taken through any pointwise lower bound $g(s)$. The required bound on $T$ decreases in every $g(s)$, so this is equivalent to using $\gamma(s)$ itself. Integrability is assumed explicitly: without it the source's integral is $+\infty$ and no $T$ qualifies, whereas Lean's integral would default to $0$. The constant $c$ is quantified before the space, the Hamiltonian and $\delta$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 225, Theorem 9.23. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

universe u

namespace QAlgorithms.Nannicini


/-- Nannicini p.225, Theorem 9.23 (Adiabatic theorem with tighter spectral bound; Thm. 28.1 in
[Childs, 2017]). There exists some constant `c` such that the statement of Thm. 9.11 holds if we
choose `T` satisfying
`T ≥ (c/δ)(‖H′(0)‖/γ(0)² + ‖H′(1)‖/γ(1)² + ∫₀¹ (‖H′(s)‖²/γ(s)³ + ‖H″(s)‖/γ(s)²) ds)`.

The constant `c` is quantified before everything it is uniform over (the space, the Hamiltonian,
`δ`; trap 8). The hypotheses are those of Theorem 9.11 other than the bound on `T`. The
instantaneous gap `γ(s)` (Def. 9.8) enters through any function `g` with
`HasGapAround (H s) (λ s) (g s)` (so `g(s) ≤ γ(s)`), bounded below by some `γ0 > 0` (Thm. 9.11's
gap `γ > 0`); the bound on `T` is decreasing in each `g(s)`, so this is equivalent to using `γ(s)`
itself. `‖H′(s)‖, ‖H″(s)‖` are the pointwise operator norms. The integrand is required to be
integrable on `[0, 1]`: when it is not, the source's integral is `+∞` and no `T` qualifies, while
Lean's integral would be the junk value `0` (trap 2). -/
theorem adiabatic_theorem_integral_gap :
    ∃ c : ℝ, ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (H H' H'' : ℝ → Matrix ι ι ℂ),
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
        HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s) →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
        HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s) →
      ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
      ∀ (φ : ℝ → EuclideanSpace ℂ ι),
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = (lam s : ℂ) • φ s) →
      ∀ (g : ℝ → ℝ) (γ0 : ℝ), 0 < γ0 →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, γ0 ≤ g s ∧ HasGapAround (H s) (lam s) (g s)) →
      IntervalIntegrable
        (fun s => specNorm (H' s) ^ 2 / g s ^ 3 + specNorm (H'' s) / g s ^ 2)
        MeasureTheory.volume 0 1 →
      ∀ (δ : ℝ), 0 < δ → ∀ (T : ℝ),
      c / δ * (specNorm (H' 0) / g 0 ^ 2 + specNorm (H' 1) / g 1 ^ 2 +
        ∫ s in (0 : ℝ)..1, (specNorm (H' s) ^ 2 / g s ^ 3 + specNorm (H'' s) / g s ^ 2)) ≤ T →
      ∀ (ψ : ℝ → EuclideanSpace ℂ ι), SolvesAdiabaticPlus H T ψ → ψ 0 = φ 0 →
      ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ := by
  sorry



end QAlgorithms.Nannicini
