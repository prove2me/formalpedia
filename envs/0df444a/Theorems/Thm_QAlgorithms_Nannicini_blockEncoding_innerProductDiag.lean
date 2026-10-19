-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_blockEncoding_innerProductDiag
-- name    : QAlgorithms.Nannicini.blockEncoding_innerProductDiag
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:52:16.887282+00:00
-- url     : https://prove2.me/theorems/55f6aacc-cc4f-47b1-9dff-c6b531d408ed
-- title:
--   Block-encoding of the diagonal matrix of inner products ⟨ϕ_j|ψ_j⟩
-- statement:
--   For each $j \in \{0,1\}^p$ let $U^{(j)}$ and $V^{(j)}$ be $(a+1)$-qubit unitaries such that
--
--   $$
--   U^{(j)}|0\rangle|0\rangle_a = |0\rangle|\psi_j\rangle + |1\rangle|\tilde\psi_j\rangle, \qquad V^{(j)}|0\rangle|0\rangle_a = |0\rangle|\phi_j\rangle + |1\rangle|\tilde\phi_j\rangle,
--   $$
--
--   for some vectors $\psi_j, \tilde\psi_j, \phi_j, \tilde\phi_j \in \mathbb{C}^{2^a}$. Let $U = \sum_j U^{(j)} \otimes |j\rangle\langle j|$ and $V = \sum_j V^{(j)}\otimes|j\rangle\langle j|$ be the $(a+p+1)$-qubit unitaries controlled by the $p$-qubit register. On $a+p+2$ qubits, ordered as a first qubit, then the $a+1$ qubits of $U^{(j)}$ (flag qubit first), then the $p$ control qubits, the unitary
--
--   $$
--   W = (I \otimes V^\dagger)(\mathrm{SWAP} \otimes I_{a+p})(I \otimes U)
--   $$
--
--   is a $(1, a+2, 0)$-block-encoding of
--
--   $$
--   \operatorname{diag}\bigl(\langle \phi_j | \psi_j\rangle\bigr)_{j = 0, \dots, 2^p-1}.
--   $$
--
--   The auxiliary register is the first $a+2$ qubits. Here $I$ acts on the first qubit and SWAP exchanges the first two qubits. So $(\langle 0|_{a+2} \otimes I)\, W\, (|0\rangle_{a+2}\otimes I) = \operatorname{diag}(\langle\phi_j|\psi_j\rangle)$ exactly.
--
--   This turns state-preparation circuits into a block-encoding of their overlaps. With Hamiltonian simulation it yields phase oracles for functions given by inner products of states.
--
--   **Formalization Note** An "$(a+2)$-block-encoding" with no other parameters is read as subnormalization $1$ and error $0$, as the proof computes the block exactly. The vectors $\psi_j$ and the garbage vectors are not separately normalized. Unitarity of $U^{(j)}$ only makes $\|\psi_j\|^2 + \|\tilde\psi_j\|^2 = 1$. The inner product $\langle\phi_j|\psi_j\rangle$ is conjugate-linear in $\phi_j$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 163, Lemma 7.20. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Nannicini_Ch07a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini




/-- Nannicini Lemma 7.20 (p.163), block-encoding of the diagonal matrix of inner products.

Let `U^(j), V^(j)` (`j ∈ {0,1}^p`) be `(a + 1)`-qubit unitaries with
`U^(j)|0⟩|0⟩_a = |0⟩|ψ_j⟩ + |1⟩|ψ̃_j⟩` and `V^(j)|0⟩|0⟩_a = |0⟩|ϕ_j⟩ + |1⟩|ϕ̃_j⟩`, and let
`U = ∑_j U^(j) ⊗ |j⟩⟨j|`, `V = ∑_j V^(j) ⊗ |j⟩⟨j|` (controlled by the last, `p`-qubit
register). On the registers (first qubit, flag qubit of `U^(j)`, `a` qubits, `p` qubits), the
unitary `(I ⊗ V†)(SWAP ⊗ I_{a+p})(I ⊗ U)` is an `(a + 2)`-block-encoding (subnormalization 1,
error 0) of `diag(⟨ϕ_j|ψ_j⟩)_{j = 0, …, 2^p − 1}`, the auxiliary register being the first
`a + 2` qubits. `I` acts on the first qubit and `SWAP` on the first two. -/
theorem blockEncoding_innerProductDiag {a p : ℕ}
    (U V : Qubits p → Matrix (Bool × Qubits a) (Bool × Qubits a) ℂ)
    (ψ ψt ϕ ϕt : Qubits p → EuclideanSpace ℂ (Qubits a))
    (hUu : ∀ j, U j ∈ Matrix.unitaryGroup (Bool × Qubits a) ℂ)
    (hVu : ∀ j, V j ∈ Matrix.unitaryGroup (Bool × Qubits a) ℂ)
    (hU : ∀ j, act (U j) (ket (false, fun _ => false)) =
      tensorVec (ket false) (ψ j) + tensorVec (ket true) (ψt j))
    (hV : ∀ j, act (V j) (ket (false, fun _ => false)) =
      tensorVec (ket false) (ϕ j) + tensorVec (ket true) (ϕt j)) :
    IsBlockEncoding ((false, (false, fun _ => false)) : Bool × (Bool × Qubits a))
      ((Matrix.of fun u v : (Bool × (Bool × Qubits a)) × Qubits p =>
          if u.1.1 = v.1.1 ∧ u.2 = v.2 then star (V u.2) u.1.2 v.1.2 else 0) *
        (Matrix.of fun u v : (Bool × (Bool × Qubits a)) × Qubits p =>
          if u.1.1 = v.1.2.1 ∧ u.1.2.1 = v.1.1 ∧ u.1.2.2 = v.1.2.2 ∧ u.2 = v.2 then 1 else 0) *
        (Matrix.of fun u v : (Bool × (Bool × Qubits a)) × Qubits p =>
          if u.1.1 = v.1.1 ∧ u.2 = v.2 then U u.2 u.1.2 v.1.2 else 0))
      1 0 (Matrix.diagonal fun j => inner ℂ (ϕ j) (ψ j)) := by
  sorry












end QAlgorithms.Nannicini
