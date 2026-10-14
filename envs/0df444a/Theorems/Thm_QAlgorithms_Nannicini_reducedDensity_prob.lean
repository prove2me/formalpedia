-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_reducedDensity_prob
-- name    : QAlgorithms.Nannicini.reducedDensity_prob
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:07.347888+00:00
-- url     : https://prove2.me/theorems/b34f6f94-7221-4c5b-8849-751984af73ac
-- title:
--   The reduced density matrix gives the correct outcome probabilities on register A
-- statement:
--   Let $AB$ be a register made of a register $A$ of $m_a$ qubits followed by a register $B$ of $m_b$ qubits. Let $\rho^{(AB)}$ be a density matrix on $AB$, and let $\rho^{(A)}=\operatorname{Tr}_B\rho^{(AB)}$ be its reduced density matrix (Definitions 1.62 and 1.64). Then for every outcome $\vec\jmath\in\{0,1\}^{m_a}$,
--
--   $$
--   \langle\vec\jmath|\rho^{(A)}|\vec\jmath\rangle=\sum_{\vec k\in\{0,1\}^{m_b}}\langle\vec\jmath|\langle\vec k|\,\rho^{(AB)}\,|\vec\jmath\rangle|\vec k\rangle .
--   $$
--
--   The left side is the probability of outcome $\vec\jmath$ when register $A$ in state $\rho^{(A)}$ is measured (Remark 1.59). The right side is the probability that measuring all qubits of $AB$ shows $\vec\jmath$ on $A$, with the outcome on $B$ discarded.
--
--   This justifies using the reduced density matrix as the state of a subsystem once the rest of the register is ignored.
--
--   **Formalization Note** The register $AB$ is indexed by pairs (outcome on $A$, outcome on $B$), and $\operatorname{Tr}_B$ is `traceRight`. A diagonal probability $\langle z|\sigma|z\rangle$ is `densityProb σ z`, the real part of the diagonal entry.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 39, Proposition 1.67. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms

open scoped ComplexOrder



/-- Nannicini p.39, Proposition 1.67: if the register `AB` (`A` of `ma` qubits first, `B` of
`mb` qubits) is in the mixed state `ρ^{(AB)}`, then the reduced density matrix
`ρ^{(A)} = Tr_B ρ^{(AB)}` gives, for every outcome `j ∈ {0,1}^{ma}`, the probability
`⟨j|ρ^{(A)}|j⟩` equal to the probability `∑_k ⟨j|⟨k|ρ^{(AB)}|j⟩|k⟩` of observing `j` on `A`
when all qubits of `AB` are measured and the outcome on `B` is discarded (Rem. 1.59). -/
theorem reducedDensity_prob {ma mb : ℕ}
    (ρ : Matrix (Qubits ma × Qubits mb) (Qubits ma × Qubits mb) ℂ) (hρ : IsDensityMatrix ρ)
    (j : Qubits ma) :
    densityProb (traceRight ρ) j = ∑ k : Qubits mb, densityProb ρ (j, k) := by sorry


end QAlgorithms.Nannicini
