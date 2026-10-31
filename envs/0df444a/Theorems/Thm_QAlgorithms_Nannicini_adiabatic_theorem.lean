-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_adiabatic_theorem
-- name    : QAlgorithms.Nannicini.adiabatic_theorem
-- status  : Disproved
-- author  : @Goku
-- created : 2026-10-13T17:51:31.301632+00:00
-- url     : https://prove2.me/theorems/b2603ee1-e9dc-436e-95f6-92417fa19666
-- title:
--   Adiabatic theorem with T ≥ (10⁴/δ²)(‖H′‖³/γ⁴ + ‖H′‖‖H″‖/γ³)
-- statement:
--   Let $H(s)$, $s \in [0,1]$, be a time-dependent Hamiltonian on a finite-dimensional space $\mathbb{C}^\iota$: each $H(s)$ is Hermitian and the entries of $H$ are twice differentiable on $[0,1]$, with entrywise derivatives $H'(s)$, $H''(s)$. Let $N_1, N_2$ bound the operator norms, $\|H'(s)\| \le N_1$ and $\|H''(s)\| \le N_2$ for all $s \in [0,1]$.
--
--   Let $\lambda : [0,1] \to \mathbb{R}$ be a continuous eigenvalue branch and $|\varphi(s)\rangle$ a unit eigenvector of $H(s)$ with eigenvalue $\lambda(s)$, for each $s \in [0,1]$. Let $\gamma > 0$ be a spectral gap around $\lambda$: for every $s$, $\lambda(s)$ is a simple eigenvalue of $H(s)$ and every other eigenvalue $\mu$ of $H(s)$ satisfies $|\mu - \lambda(s)| \ge \gamma$.
--
--   Let $\delta > 0$ and let $T$ satisfy
--
--   $$
--   T \ge \frac{10^4}{\delta^2}\left(\frac{N_1^3}{\gamma^4} + \frac{N_1 N_2}{\gamma^3}\right).
--   $$
--
--   Let $|\psi(s)\rangle$ solve the adiabatic evolution
--
--   $$
--   \frac{d|\psi(s)\rangle}{ds} = iT\,H(s)|\psi(s)\rangle, \quad s \in [0,1], \qquad |\psi(0)\rangle = |\varphi(0)\rangle .
--   $$
--
--   Then there is $\theta \in \mathbb{R}$ with
--
--   $$
--   \bigl\| e^{i\theta} |\psi(1)\rangle - |\varphi(1)\rangle \bigr\| \le \delta .
--   $$
--
--   This is the adiabatic theorem in the form of Ambainis and Regev. A slow enough evolution carries an eigenvector of $H(0)$ to the corresponding eigenvector of $H(1)$, up to a global phase. It is the basis of adiabatic optimization: start in the known ground state of a simple Hamiltonian and interpolate to a Hamiltonian that encodes the problem.
--
--   **Formalization Note** The source's $\|H'\| = \max_s\|H'(s)\|$, $\|H''\|$ and $\gamma = \min_s \gamma(s)$ (Defs. 9.6–9.9) are replaced by arbitrary bounds $N_1, N_2$ and an arbitrary lower bound $\gamma > 0$ on the instantaneous gaps. The required lower bound on $T$ increases in $N_1, N_2$ and decreases in $\gamma$, so this is equivalent to the source's statement and avoids junk values of real suprema. Derivatives at $s = 0, 1$ are one-sided. Only the precise final-state claim is stated: the source's "approximately remains … for all $s$" carries no stated error.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 212, Theorem 9.11. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.Stabilizer


/-- Nannicini pp.212–213, Theorem 9.11 (Adiabatic theorem). Let `H(s)` be a time-dependent
Hamiltonian, let `λ(s)` be an eigenvalue of `H(s)`, and let `|φ(s)⟩` be an eigenstate of `H(s)`
with eigenvalue `λ(s)`. Assume that there is a spectral gap `γ > 0` around `λ(s)`. Assume further
that, from the initial state `|φ(0)⟩`, we apply the time evolution `d|ψ(s)⟩/ds = iT H(s)|ψ(s)⟩`,
`s ∈ [0, 1]`, `|ψ(0)⟩ = |φ(0)⟩`, and for some `δ > 0`, `T` satisfies
`T ≥ (10⁴/δ²)(‖H′‖³/γ⁴ + ‖H′‖‖H″‖/γ³)`. Then the system approximately remains in the
instantaneous eigenstate `|φ(s)⟩` with eigenvalue `λ(s)` for all `s`, and in particular, the final
state `|ψ(1)⟩` has Euclidean distance at most `δ` from `|φ(1)⟩`, up to global phase:
`‖e^{iθ}|ψ(1)⟩ − |φ(1)⟩‖ ≤ δ` for some `θ`.

Stated is the precise claim, the "in particular" about `ψ(1)`; the unquantified "approximately
remains … for all s" carries no stated error. Hermiticity of `H(s)` is part of `HasGapAround`.
`‖H′‖, ‖H″‖, γ` are the bounds `N1, N2, γ` of the module docstring. -/
theorem adiabatic_theorem {ι : Type*} [Fintype ι] [DecidableEq ι] (H H' H'' : ℝ → Matrix ι ι ℂ)
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
