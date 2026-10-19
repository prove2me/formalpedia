-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_exp_unitary_conj
-- name    : QAlgorithms.Nannicini.exp_unitary_conj
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:51:01.722986+00:00
-- url     : https://prove2.me/theorems/026bcb5c-18c8-43e4-9774-a1ec0df82ef8
-- title:
--   Unitary conjugation commutes with the matrix exponential: e^{iUHU†t} = U e^{iHt} U†
-- statement:
--   Let $n \ge 0$, let $U$ be a unitary $2^n \times 2^n$ matrix, let $\mathcal{H}$ be a Hamiltonian on $n$ qubits, that is, a Hermitian $2^n \times 2^n$ complex matrix, and let $t \in \mathbb{R}$. With the matrix exponential $e^A = \sum_{k=0}^\infty A^k / k!$,
--
--   $$
--   e^{iU\mathcal{H}U^\dagger t} = U\, e^{i\mathcal{H}t}\, U^\dagger.
--   $$
--
--   This is what makes diagonalizable Hamiltonians easy to simulate: if $U$ diagonalizes $\mathcal{H}$, simulating $\mathcal{H}$ reduces to applying $U^\dagger$, a diagonal phase, and $U$.
--
--   **Formalization Note** The matrix exponential is Mathlib's power series `NormedSpace.exp`; $U^\dagger$ is the conjugate transpose (`star U`). Hermiticity of $\mathcal{H}$ is kept because the source says Hamiltonian (Def. 6.1), although the identity holds for every square matrix.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 137, Proposition 6.12. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini


/-- Nannicini p.137, Proposition 6.12. For any unitary `U` and Hamiltonian `H` (a Hermitian
`2^n × 2^n` matrix, Def. 6.1) and any real time `t`, `e^{iUHU†t} = U e^{iHt} U†`. -/
theorem exp_unitary_conj {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (H : Matrix (Qubits n) (Qubits n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • (U * H * star U)) =
      U * NormedSpace.exp ((Complex.I * (t : ℂ)) • H) * star U := by
  sorry

end QAlgorithms.Nannicini
