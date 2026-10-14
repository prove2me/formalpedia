-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_adiabatic_theorem_zero
-- name    : QAlgorithms.Nannicini.adiabatic_theorem_zero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:51:29.848076+00:00
-- url     : https://prove2.me/theorems/c55ba26f-7bbe-426b-89be-1ebba5c73cb9
-- title:
--   Adiabatic theorem when the tracked eigenvalue is identically 0
-- statement:
--   Let $H(s)$, $s \in [0,1]$, be a time-dependent Hamiltonian on $\mathbb{C}^\iota$: each $H(s)$ is Hermitian and the entries of $H$ are twice differentiable on $[0,1]$, with entrywise derivatives $H'$, $H''$ bounded by $\|H'(s)\| \le N_1$ and $\|H''(s)\| \le N_2$ in operator norm for all $s$.
--
--   Suppose that for every $s \in [0,1]$, $|\varphi(s)\rangle$ is a unit vector with $H(s)|\varphi(s)\rangle = 0$. Let $\gamma > 0$ be a spectral gap around $0$: $0$ is a simple eigenvalue of every $H(s)$, and every other eigenvalue has absolute value at least $\gamma$.
--
--   Let $\delta > 0$ and let $T$ satisfy
--
--   $$
--   T \ge \frac{10^3}{\delta^2}\max\left\{\frac{N_1^3}{\gamma^4}, \frac{N_1 N_2}{\gamma^3}\right\}.
--   $$
--
--   If $|\psi(s)\rangle$ solves $\frac{d|\psi(s)\rangle}{ds} = iT\,H(s)|\psi(s)\rangle$ on $[0,1]$ with $|\psi(0)\rangle = |\varphi(0)\rangle$, then for some $\theta \in \mathbb{R}$
--
--   $$
--   \bigl\| e^{i\theta}|\psi(1)\rangle - |\varphi(1)\rangle \bigr\| \le \delta .
--   $$
--
--   This special case, where the tracked eigenvalue is identically zero, is the one proved in detail in the notes. The general adiabatic theorem follows from it by shifting $H(s)$ by $\lambda(s)I$.
--
--   **Formalization Note** As for the general theorem, the max norms and the minimum gap are replaced by arbitrary bounds $N_1, N_2$ and a lower bound $\gamma$ on the gaps, which is equivalent by monotonicity. The constant $10^3$ is the printed one.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 218, Theorem 9.17. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.Stabilizer



/-- Nannicini p.218, Theorem 9.17 (Special case of the adiabatic theorem). Let `H(s)` be a
time-dependent Hamiltonian, and let `|φ(s)⟩` be an eigenstate of `H(s)` with eigenvalue
`λ(s) = 0` for all `s ∈ [0, 1]`. Assume that there is a spectral gap `γ > 0` around `λ(s) = 0`,
i.e., all other eigenvalues are at least `γ` in absolute value. Assume further that, from the
initial state `|φ(0)⟩`, we apply the time evolution `d|ψ(s)⟩/ds = iT H(s)|ψ(s)⟩`, `s ∈ [0, 1]`,
`|ψ(0)⟩ = |φ(0)⟩`, and for some `δ > 0`, `T` satisfies
`T ≥ (10³/δ²) max{‖H′‖³/γ⁴, ‖H′‖‖H″‖/γ³}`. Then the system approximately remains in the
instantaneous eigenstate `|φ(s)⟩` with eigenvalue `0` for all `s`, and in particular, the final
state `|ψ(1)⟩` has Euclidean distance at most `δ` from `|φ(1)⟩`, up to global phase:
`‖e^{iθ}|ψ(1)⟩ − |φ(1)⟩‖ ≤ δ` for some `θ`.

The constant `10³` is the printed one (also Eq. (9.25)). Conventions as in `adiabatic_theorem`;
the gap is `HasGapAround (H s) 0 γ` (`0` a simple eigenvalue, all others `≥ γ` in absolute value). -/
theorem adiabatic_theorem_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (H H' H'' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (hH'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s)
    (φ : ℝ → EuclideanSpace ℂ ι) (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = 0)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) 0 γ)
    (N1 N2 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (hN2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H'' s) ≤ N2)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ)
    (hT : 10 ^ 3 / δ ^ 2 * max (N1 ^ 3 / γ ^ 4) (N1 * N2 / γ ^ 3) ≤ T)
    (ψ : ℝ → EuclideanSpace ℂ ι) (hψ : SolvesAdiabaticPlus H T ψ) (hψ0 : ψ 0 = φ 0) :
    ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ := by
  sorry



end QAlgorithms.Nannicini
