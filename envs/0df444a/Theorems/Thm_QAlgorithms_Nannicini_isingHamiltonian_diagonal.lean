-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_isingHamiltonian_diagonal
-- name    : QAlgorithms.Nannicini.isingHamiltonian_diagonal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:51:35.298599+00:00
-- url     : https://prove2.me/theorems/785b3680-b59b-4f12-8acc-205f17a64788
-- title:
--   The Ising Hamiltonian is diagonal with the QUBO objective values
-- statement:
--   Let $n \ge 0$, let $A \in \mathbb{R}^{n\times n}$ and $c \in \mathbb{R}^n$ be the data of the $\pm1$ form (9.3) of a QUBO problem. For $j = 1, \dots, n$ let $\sigma_j^Z = I \otimes \cdots \otimes Z \otimes \cdots \otimes I$ be the Pauli $Z$ matrix acting on qubit $j$ of an $n$-qubit register, with the identity on all other qubits. Define the Hamiltonian
--
--   $$
--   H := \sum_{j,k=1}^n A_{jk}\, \sigma_j^Z \sigma_k^Z + \sum_{j=1}^n c_j\, \sigma_j^Z .
--   $$
--
--   For a bit string $x \in \{0,1\}^n$ put $z = \mathbf{1} - 2x \in \{-1,+1\}^n$. Then
--
--   1. $\langle x | H | x \rangle = z^\top A z + c^\top z$ for every $x \in \{0,1\}^n$;
--   2. $\langle y | H | w \rangle = 0$ for all basis strings $y \ne w$.
--
--   Thus $H$ is diagonal in the computational basis and carries the objective values of problem (9.3), up to the constant shift $b$, on its diagonal. Minimizing the QUBO is therefore the problem of finding the minimum eigenvalue of $H$, which is what the adiabatic algorithm targets.
--
--   **Formalization Note** $\sigma_j^Z$ is the Pauli $Z$ embedded on wire $j$ (the source's qubit $j+1$). The matrix entries $H_{xx}$ and $H_{yw}$ are complex, and the diagonal value is the real number $z^\top A z + c^\top z$ cast to $\mathbb{C}$. $A$ and $c$ are arbitrary, as the proof does not use their QUBO-derived form.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 209, Proposition 9.4. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.Stabilizer

/-- Nannicini pp.209–210, Proposition 9.4. The Hamiltonian
`H := Σ_{j,k=1}^n A_jk σ_j^Z σ_k^Z + Σ_{j=1}^n c_j σ_j^Z` satisfies the properties:
`⟨x|H|x⟩ = zᵀAz + cᵀz ∀x ∈ {0,1}^n`, `⟨j|H|k⟩ = 0 ∀j ≠ k`, where `z = 1 − 2x ∈ {−1,+1}^n`.

`A ∈ ℝ^{n×n}` and `c ∈ ℝ^n` are the data of problem (9.3), arbitrary (the proof does not use
`A = Q/4`, `c = −Qᵀ1/2`). `σ_j^Z` (Eq. (9.4)) is the Pauli `Z` on wire `j` (the source's qubit
`j + 1`), identity elsewhere; `⟨y|H|w⟩` is the matrix entry `H y w`; `x_j` is read as `0/1` by
`boolPoint`. -/
theorem isingHamiltonian_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    let σ : Fin n → Matrix (Qubits n) (Qubits n) ℂ := fun j => CliffordOp.mat (CliffordOp.pauli j Pauli.Z)
    let H : Matrix (Qubits n) (Qubits n) ℂ :=
      ∑ j : Fin n, ∑ k : Fin n, ((A j k : ℝ) : ℂ) • (σ j * σ k) + ∑ j : Fin n, ((c j : ℝ) : ℂ) • σ j
    (∀ x : Qubits n,
      H x x = (((∑ j : Fin n, ∑ k : Fin n, A j k * (1 - 2 * boolPoint x j) * (1 - 2 * boolPoint x k)) +
        ∑ j : Fin n, c j * (1 - 2 * boolPoint x j) : ℝ) : ℂ)) ∧
      ∀ y w : Qubits n, y ≠ w → H y w = 0 := by
  sorry





end QAlgorithms.Nannicini
