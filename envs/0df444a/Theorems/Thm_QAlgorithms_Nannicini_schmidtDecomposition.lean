-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_schmidtDecomposition
-- name    : QAlgorithms.Nannicini.schmidtDecomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:52:26.138527+00:00
-- url     : https://prove2.me/theorems/6b553ac0-e665-496f-9b39-5a82528bf259
-- title:
--   Schmidt decomposition
-- statement:
--   Let $AB$ be a register made of a register $A$ of $m_a$ qubits followed by a register $B$ of $m_b$ qubits. Let $|\psi\rangle$ be a pure state of $AB$, that is, a unit vector. Then there exist a finite index set $\{1,\dots,r\}$, an orthonormal family $|\phi^A_1\rangle,\dots,|\phi^A_r\rangle$ of states of $A$, an orthonormal family $|\phi^B_1\rangle,\dots,|\phi^B_r\rangle$ of states of $B$, and nonnegative reals $\lambda_1,\dots,\lambda_r$ with $\sum_j\lambda_j^2=1$, such that
--
--   $$
--   |\psi\rangle=\sum_{j=1}^r\lambda_j\,|\phi^A_j\rangle|\phi^B_j\rangle .
--   $$
--
--   This is the singular value decomposition rephrased for bipartite pure states. Classical simulation algorithms for quantum circuits use it.
--
--   **Formalization Note** The source leaves the index set unspecified; here it is `Fin r` for an existentially chosen `r`.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 40, Theorem 1.70. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms

open scoped ComplexOrder




/-- Nannicini p.40, Theorem 1.70 (Schmidt decomposition): every pure state `|ψ⟩` of a composite
register `AB` can be written `|ψ⟩ = ∑_j λ_j |φ_j^A⟩|φ_j^B⟩` with orthonormal states `φ_j^A` of
`A`, orthonormal states `φ_j^B` of `B`, and nonnegative reals `λ_j` with `∑_j λ_j² = 1`. The
index set of `j`, left unspecified by the source, is a finite `Fin r`. -/
theorem schmidtDecomposition {ma mb : ℕ} (ψ : EuclideanSpace ℂ (Qubits ma × Qubits mb))
    (hψ : IsState ψ) :
    ∃ (r : ℕ) (lam : Fin r → ℝ) (φA : Fin r → EuclideanSpace ℂ (Qubits ma))
      (φB : Fin r → EuclideanSpace ℂ (Qubits mb)),
      Orthonormal ℂ φA ∧ Orthonormal ℂ φB ∧ (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j ^ 2 = 1 ∧
        ψ = ∑ j, (lam j : ℂ) • tensorVec (φA j) (φB j) := by sorry

end QAlgorithms.Nannicini
