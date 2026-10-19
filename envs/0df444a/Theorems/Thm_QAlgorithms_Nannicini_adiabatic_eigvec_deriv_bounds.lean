-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_adiabatic_eigvec_deriv_bounds
-- name    : QAlgorithms.Nannicini.adiabatic_eigvec_deriv_bounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:51:34.585678+00:00
-- url     : https://prove2.me/theorems/e7cb0f01-9fd1-4187-93d6-1722d4cd50f5
-- title:
--   Derivative bounds for the phase-fixed instantaneous zero eigenvector
-- statement:
--   Let $H(s)$, $s \in [0,1]$, be a time-dependent Hamiltonian on $\mathbb{C}^\iota$ with twice differentiable entries, entrywise derivatives $H'$, $H''$, and operator-norm bounds $\|H'(s)\| \le N_1$, $\|H''(s)\| \le N_2$ for all $s$. Let $|\varphi(s)\rangle$ be a unit vector with $H(s)|\varphi(s)\rangle = 0$ for every $s \in [0,1]$. Let $\gamma > 0$ be a spectral gap around $0$: $0$ is a simple eigenvalue of each $H(s)$ and all other eigenvalues have absolute value at least $\gamma$.
--
--   Assume $s \mapsto |\varphi(s)\rangle$ is twice differentiable on $[0,1]$, with entrywise derivatives $|\varphi'(s)\rangle$, $|\varphi''(s)\rangle$, and that its phase is fixed by
--
--   $$
--   \langle \varphi'(s) | \varphi(s) \rangle = 0 \qquad \text{for all } s \in [0,1].
--   $$
--
--   Then for every $s \in [0,1]$
--
--   $$
--   \bigl\| |\varphi'(s)\rangle \bigr\| \le \frac{N_1}{\gamma}, \qquad \bigl\| |\varphi''(s)\rangle \bigr\| \le \frac{N_2}{\gamma} + \frac{3 N_1^2}{\gamma^2}.
--   $$
--
--   These bounds control how fast the tracked eigenvector moves. They give the estimates $\|p_1\| \le \|H'\|/(\gamma N)$ and Eq. (9.23) in the proof of the adiabatic theorem.
--
--   **Formalization Note** The source's max norms $\|\,|\varphi'\rangle\|$, $\|\,|\varphi''\rangle\|$, $\|H'\|$, $\|H''\|$ (Def. 9.6) are expressed pointwise against bounds $N_1, N_2$, which is equivalent. Of the context of Theorem 9.17 only the Hamiltonian, its zero eigenvector and the gap are used: the evolution $\psi$, $T$ and $\delta$ play no role in the lemma. Derivatives at the endpoints are one-sided.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 218, Lemma 9.18. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.Stabilizer




/-- Nannicini p.218, Lemma 9.18 (Lem. 3.2 in [Ambainis and Regev, 2004]). In the context of
Thm. 9.17, assume the phase of `|φ(s)⟩` is chosen so that `⟨φ′(s)|φ(s)⟩ = 0`. Then
`‖|φ′⟩‖ ≤ ‖H′‖/γ` and `‖|φ″⟩‖ ≤ ‖H″‖/γ + 3‖H′‖²/γ²`.

The context of Thm. 9.17 that the lemma uses is the Hamiltonian and its zero eigenvector with gap
`γ`; the evolution `ψ`, `T`, `δ` play no role and are omitted. `φ′, φ″` are the entrywise
derivatives (Rem. 9.19), functions `φ' φ''` with `HasDerivWithinAt` on `[0, 1]` (twice
differentiability of `φ` is implicit, since `φ′, φ″` appear). The max norms `‖|φ′⟩‖, ‖|φ″⟩‖`
(Def. 9.6) are bounded pointwise for every `s`, which is equivalent. -/
theorem adiabatic_eigvec_deriv_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' H'' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (hH'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s)
    (φ φ' φ'' : ℝ → EuclideanSpace ℂ ι)
    (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = 0)
    (hφ' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' s) (Set.Icc 0 1) s)
    (hφ'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ' (φ'' s) (Set.Icc 0 1) s)
    (hphase : ∀ s ∈ Set.Icc (0 : ℝ) 1, inner ℂ (φ' s) (φ s) = 0)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) 0 γ)
    (N1 N2 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (hN2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H'' s) ≤ N2) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖φ' s‖ ≤ N1 / γ ∧ ‖φ'' s‖ ≤ N2 / γ + 3 * N1 ^ 2 / γ ^ 2 := by
  sorry


end QAlgorithms.Nannicini
