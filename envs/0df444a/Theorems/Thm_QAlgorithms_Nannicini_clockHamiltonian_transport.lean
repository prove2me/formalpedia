-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_clockHamiltonian_transport
-- name    : QAlgorithms.Nannicini.clockHamiltonian_transport
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:51:15.319069+00:00
-- url     : https://prove2.me/theorems/68047386-3f93-487a-8eb6-6c5eefdcf52e
-- title:
--   Phase condition under which the clock Hamiltonian transports |u^(1)⟩ to e^{iϕ}|u^(N)⟩
-- statement:
--   Let $N \ge 1$ and let $|u^{(1)}\rangle, \dots, |u^{(N)}\rangle$ be the standard basis of $\mathbb{C}^N$. Let $H_B$ be the clock Hamiltonian, the real symmetric tridiagonal $N \times N$ matrix with zero diagonal and off-diagonal entries
--
--   $$
--   (H_B)_{j,j+1} = (H_B)_{j+1,j} = \tfrac12\sqrt{j(N-j)}, \qquad j = 1, \dots, N-1,
--   $$
--
--   and let $M_s = \sum_{j=1}^N |u^{(j)}\rangle\langle u^{(N+1-j)}|$ be the mirror permutation. Let $|\psi_1\rangle, \dots, |\psi_N\rangle$ be an orthonormal basis of eigenvectors of $H_B$, with $H_B|\psi_j\rangle = \lambda_j|\psi_j\rangle$, and let $S = \{j : M_s|\psi_j\rangle = |\psi_j\rangle\}$ be the indices of the symmetric eigenvectors. Suppose $t, \phi \in \mathbb{R}$ are such that for every $j$ with $\langle\psi_j|u^{(1)}\rangle \ne 0$,
--
--   $$
--   e^{-i\lambda_j t} = e^{i\phi} \text{ if } j \in S, \qquad e^{-i\lambda_j t} = -e^{i\phi} \text{ if } j \notin S.
--   $$
--
--   Then
--
--   $$
--   e^{-iH_B t}\,|u^{(1)}\rangle = e^{i\phi}\,|u^{(N)}\rangle.
--   $$
--
--   This is the core of the argument that Hamiltonian simulation is BQP-complete: evolving the clock register under $H_B$ (for $t = \pi$, where the condition holds) moves the clock from its first to its last position, so the circuit's unitaries are applied in order.
--
--   **Formalization Note** Indices are 0-based in Lean: $|u^{(1)}\rangle$ is the basis vector at index $0$ and $|u^{(N)}\rangle$ at index $N-1$. The matrix exponential is Mathlib's power series. The statement holds for every orthonormal eigenbasis; every eigenvector of $H_B$ is either symmetric or antisymmetric, because $H_B$ has simple spectrum, so $j \notin S$ means $M_s|\psi_j\rangle = -|\psi_j\rangle$, as in the source.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 136, Proposition 6.9. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- Nannicini p.136, Proposition 6.9. Let `H_B` be the `N × N` clock Hamiltonian of p.135
(zero diagonal, `(H_B)_{j,j+1} = (H_B)_{j+1,j} = ½√(j(N−j))`, the frozen `clockHamiltonian N`)
and `M_s = Σ_j |u^(j)⟩⟨u^(N+1−j)|` the mirror matrix (`mirrorMatrix N`). For every orthonormal
eigenbasis `(ψ_j)` of `H_B` with eigenvalues `λ_j`, let `S` be the indices with `M_s ψ_j = ψ_j`
(symmetric). If a time `t` and an angle `ϕ` satisfy, for every `j` with `⟨ψ_j|u^(1)⟩ ≠ 0`,
`e^{−iλ_j t} = e^{iϕ}` when `j ∈ S` and `e^{−iλ_j t} = −e^{iϕ}` when `j ∉ S`, then
`e^{−iH_B t}|u^(1)⟩ = e^{iϕ}|u^(N)⟩`. -/
theorem clockHamiltonian_transport {N : ℕ} (hN : 0 < N)
    (ψ : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (lam : Fin N → ℝ)
    (heig : ∀ j, act (clockHamiltonian N) (ψ j) = (lam j : ℂ) • ψ j)
    (t ϕ : ℝ)
    (hphase : ∀ j, inner ℂ (ψ j) (ket (⟨0, hN⟩ : Fin N)) ≠ 0 →
      (act (mirrorMatrix N) (ψ j) = ψ j →
        Complex.exp (-(Complex.I * (lam j : ℂ) * (t : ℂ))) = Complex.exp ((ϕ : ℂ) * Complex.I)) ∧
      (act (mirrorMatrix N) (ψ j) ≠ ψ j →
        Complex.exp (-(Complex.I * (lam j : ℂ) * (t : ℂ))) = -Complex.exp ((ϕ : ℂ) * Complex.I))) :
    act (NormedSpace.exp (-(Complex.I * (t : ℂ)) • clockHamiltonian N)) (ket (⟨0, hN⟩ : Fin N)) =
      Complex.exp ((ϕ : ℂ) * Complex.I) • ket (⟨N - 1, by omega⟩ : Fin N) := by
  sorry


end QAlgorithms.Nannicini
