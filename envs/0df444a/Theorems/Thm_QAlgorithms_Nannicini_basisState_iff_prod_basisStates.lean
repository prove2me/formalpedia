-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_basisState_iff_prod_basisStates
-- name    : QAlgorithms.Nannicini.basisState_iff_prod_basisStates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:51:00.258579+00:00
-- url     : https://prove2.me/theorems/87fed339-4297-49e0-93b8-84cda15572c7
-- title:
--   Basis states are exactly tensor products of single-qubit basis states
-- statement:
--   Let $q>1$ and let $|\psi\rangle\in(\mathbb C^2)^{\otimes q}$ be a $q$-qubit quantum state, i.e. a unit vector. Recall (Def. 1.16) that $|\psi\rangle$ is a *basis state* if $|\psi\rangle=\alpha_k|\vec k\rangle$ for some $\vec k\in\{0,1\}^q$ and some $\alpha_k\in\mathbb C$ with $|\alpha_k|^2=1$. Then $|\psi\rangle$ is a basis state if and only if there are single-qubit states $|\psi_1\rangle,\dots,|\psi_q\rangle\in\mathbb C^2$, each of which is a basis state, such that
--
--   $$
--   |\psi\rangle=|\psi_1\rangle\otimes|\psi_2\rangle\otimes\cdots\otimes|\psi_q\rangle .
--   $$
--
--   The statement shows that basis states are always product states, in contrast with superpositions, which can be entangled.
--
--   **Formalization Note** The $q$-qubit register is indexed by $\{0,1\}^q$ with the first qubit as the most significant bit; the tensor product of the single-qubit states is the vector whose $\vec z$-coordinate is $\prod_{i}\langle z_i|\psi_i\rangle$, with qubit $i$ of the source being the $i$-th factor. Being a basis state already forces unit norm, so the unit-norm hypotheses are stated for fidelity to the source but are redundant.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 14, Proposition 1.19. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

namespace QAlgorithms.Nannicini


/-- Nannicini p.14, Proposition 1.19: a `q`-qubit register, `q > 1`, is in a basis state
(Def. 1.16: `|ψ⟩ = α_k |k⟩` with `|α_k|² = 1`) if and only if its state is the tensor product
`|ψ_1⟩ ⊗ ⋯ ⊗ |ψ_q⟩` of `q` single-qubit states each of which is a basis state. Wire `i` is the
source's qubit `i + 1` (the first qubit is the most significant). -/
theorem basisState_iff_prod_basisStates {q : ℕ} (hq : 1 < q)
    (ψ : EuclideanSpace ℂ (Qubits q)) (hψ : IsState ψ) :
    IsBasisState ψ ↔ ∃ φ : Fin q → EuclideanSpace ℂ Bool,
      (∀ i, IsState (φ i) ∧ IsBasisState (φ i)) ∧ ψ = prodState φ := by
  sorry




end QAlgorithms.Nannicini
