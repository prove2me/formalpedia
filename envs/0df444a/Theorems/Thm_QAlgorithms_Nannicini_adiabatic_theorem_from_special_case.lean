-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_adiabatic_theorem_from_special_case
-- name    : QAlgorithms.Nannicini.adiabatic_theorem_from_special_case
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:51:03.567719+00:00
-- url     : https://prove2.me/theorems/56021457-ac06-4088-aa06-775e7bb13582
-- title:
--   The T-bound of Theorem 9.11 suffices (derived from Theorem 9.17)
-- statement:
--   This corollary restates the conclusion of the adiabatic theorem (Theorem 9.11) under that theorem's hypotheses. The source records it separately because it is derived from the special case $\lambda \equiv 0$ (Theorem 9.17) by passing to $\hat H(s) = H(s) - \lambda(s) I$.
--
--   Let $H(s)$, $s \in [0,1]$, be a time-dependent Hamiltonian on $\mathbb{C}^\iota$: each $H(s)$ is Hermitian and the entries of $H$ are twice differentiable on $[0,1]$, with entrywise derivatives $H'(s), H''(s)$ satisfying $\|H'(s)\| \le N_1$ and $\|H''(s)\| \le N_2$ in operator norm for all $s$. Let $\lambda : [0,1] \to \mathbb{R}$ be continuous and let $|\varphi(s)\rangle$ be a unit eigenvector of $H(s)$ with eigenvalue $\lambda(s)$. Let $\gamma > 0$ be a spectral gap around $\lambda$: $\lambda(s)$ is a simple eigenvalue of $H(s)$ and every other eigenvalue lies at distance at least $\gamma$ from it, for every $s$. Let $\delta > 0$ and
--
--   $$
--   T \ge \frac{10^4}{\delta^2}\left(\frac{N_1^3}{\gamma^4} + \frac{N_1 N_2}{\gamma^3}\right).
--   $$
--
--   If $|\psi(s)\rangle$ solves $\frac{d|\psi(s)\rangle}{ds} = iT\,H(s)|\psi(s)\rangle$ on $[0,1]$ with $|\psi(0)\rangle = |\varphi(0)\rangle$, then
--
--   $$
--   \bigl\| e^{i\theta}|\psi(1)\rangle - |\varphi(1)\rangle \bigr\| \le \delta \quad \text{for some } \theta \in \mathbb{R}.
--   $$
--
--   This completes the proof of the general adiabatic theorem from the zero-eigenvalue case.
--
--   **Formalization Note** The binders are identical to those of the statement of Theorem 9.11. The source's $\|H'\| = \max_s \|H'(s)\|$, $\|H''\|$ and $\gamma = \min_s \gamma(s)$ are replaced by arbitrary bounds $N_1, N_2$ and a lower bound $\gamma$, which is equivalent by monotonicity.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 223, Corollary 9.21. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

universe u

namespace QAlgorithms.Nannicini

/-- Nannicini p.223, Corollary 9.21. The lower bound for `T` stated in Thm. 9.11 suffices to ensure
adiabatic evolution, i.e., a final state such that `‖e^{iθ}|ψ(1)⟩ − |φ(1)⟩‖ ≤ δ` for some `θ`.

The corollary is the conclusion of Theorem 9.11 under Theorem 9.11's hypotheses (pp.212–213), the
source restating it to record that it follows from Theorem 9.17 via `Ĥ(s) = H(s) − λ(s)I`. The
binders are those of `adiabatic_theorem` (Ch09a): `‖H′‖, ‖H″‖, γ` are the bounds `N1, N2, γ`;
Hermiticity of `H(s)` is part of `HasGapAround`. -/
theorem adiabatic_theorem_from_special_case {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' H'' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (hH'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s)
    (lam : ℝ → ℝ) (hlam : ContinuousOn lam (Set.Icc 0 1)) (φ : ℝ → EuclideanSpace ℂ ι)
    (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = (lam s : ℂ) • φ s)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) (lam s) γ)
    (N1 N2 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (hN2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H'' s) ≤ N2)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ)
    (hT : 10 ^ 4 / δ ^ 2 * (N1 ^ 3 / γ ^ 4 + N1 * N2 / γ ^ 3) ≤ T)
    (ψ : ℝ → EuclideanSpace ℂ ι) (hψ : SolvesAdiabaticPlus H T ψ) (hψ0 : ψ 0 = φ 0) :
    ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ := by
  sorry




end QAlgorithms.Nannicini
