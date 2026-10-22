-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_no_cloning
-- name    : QAlgorithms.Nannicini.no_cloning
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:51:57.984219+00:00
-- url     : https://prove2.me/theorems/4654f02d-dded-4cf9-8ae4-649ba7d1aff8
-- title:
--   No-cloning principle
-- statement:
--   Let $q\ge 0$. There is no unitary matrix $U$ acting on two $q$-qubit registers, i.e. on $(\mathbb C^2)^{\otimes q}\otimes(\mathbb C^2)^{\otimes q}$, such that for every $q$-qubit quantum state $|\psi\rangle$ (unit vector)
--
--   $$
--   U\big(|\psi\rangle_q\,|\vec 0\rangle_q\big)=|\psi\rangle_q\,|\psi\rangle_q .
--   $$
--
--   A single unitary cannot copy every quantum state; in particular the destructive effect of measurement cannot be avoided by cloning the state beforehand.
--
--   **Formalization Note** The two registers are indexed by pairs of bit strings, first register first; this is the source's $(\mathbb C^2)^{\otimes 2q}$ with the first $q$ qubits forming the first register. Equality is exact, as in the source. The statement also holds at $q=0$, so no positivity hypothesis on $q$ is added.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 23, Theorem 1.32. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

namespace QAlgorithms.Nannicini




/-- Nannicini p.23, Theorem 1.32 (No-cloning principle): there is no unitary matrix on two
`q`-qubit registers that maps `|ψ⟩_q |0⟩_q` to `|ψ⟩_q |ψ⟩_q` for every `q`-qubit quantum state
`|ψ⟩`. -/
theorem no_cloning (q : ℕ) :
    ¬ ∃ U : Matrix (Qubits q × Qubits q) (Qubits q × Qubits q) ℂ,
      U ∈ Matrix.unitaryGroup (Qubits q × Qubits q) ℂ ∧
      ∀ ψ : EuclideanSpace ℂ (Qubits q), IsState ψ →
        act U (tensorVec ψ (zeroKet q)) = tensorVec ψ ψ := by
  sorry


end QAlgorithms.Nannicini
