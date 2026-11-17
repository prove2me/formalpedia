-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_48
-- name    : SingleInteraction.Supplement.theorem_48
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:06:27.29563+00:00
-- url     : https://prove2.me/theorems/a37bcf00-7052-4bb5-a40b-d6f50d137304
-- title:
--   Theorem 48 — pinned single-interaction compiler: $V^\dagger\tilde KV=K$, binary and base-3 selectors
-- statement:
--   Let $A=\{h^{(1)},\dots,h^{(m)}\}$ be $k$-qubit Hermitian interactions. For each of the two selectors below there are one Hermitian interaction $\tilde h$ on $k'$ qubits and one normalized state $|\Psi_{\mathrm{ancilla}}\rangle$ on $p$ pinned qubits, both depending only on $A$, such that the following holds. For every working register $W$ and every
--   $$K=\sum_{i=1}^Mh^{(j_i)}_{V_i}$$
--   with ordered $k$-tuples $V_i$ of distinct qubits of $W$ and pairwise distinct pairs $(V_i,j_i)$, there are pairwise distinct ordered $k'$-tuples $e_1,\dots,e_M$ of distinct qubits of $W\sqcup A$ such that $\tilde K=\sum_i\tilde h_{e_i}$ and $V|\psi\rangle=|\psi\rangle_W\otimes|\Psi_{\mathrm{ancilla}}\rangle_A$ satisfy
--   $$V^\dagger\tilde KV=K.$$
--   Moreover, if every $h^{(j)}$ has polynomial-time computable entries, so does $\tilde h$.
--
--   1. Binary selector: $k'=k+\lceil\log_2m\rceil$ and $p=2\lceil\log_2m\rceil$.
--   2. Base-3 Pauli selector: $k'=k+\lceil\log_3m\rceil$ and $p=3\lceil\log_3m\rceil$.
--
--   In particular, for constant $k$ and $m$ the locality overhead and the number of pinned qubits are constant. The compiler turns a Hamiltonian over a fixed finite interaction set into an unweighted single-interaction Hamiltonian in a pinned sector, exactly.
--
--   **Formalization Note** $\lceil\log_bm\rceil$ is `Nat.clog b m`; the register is `Fin NW ⊕ Fin p`.
--
--   Differences from the source:
--   - generalization: a fixed finite set A = {h(1), …, h(m)} → an indexed family A : Fin m → k-qubit Hermitian matrices, members possibly repeated; reason: a set is the case of an injective enumeration; the paper itself treats members differing by a scalar as distinct elements (p.36)
--   - reading: a single interaction matrix h̃ → h̃ Hermitian; reason: Definition 31 requires the common interaction to be Hermitian; both selector constructions are
--   - encoding: K̃ built from applications of h̃ on the routed tuples (V_i, U_i) → K̃ = Σ_i h̃_{e_i} for some pairwise distinct injective tuples e_i into W ⊔ A; reason: the paper verifies exactly these ordered-hyperedge conditions in the proof (p.39); the particular routing is not part of the statement
--   - reading: In particular, if k and m are constants, then both the locality overhead and the number of pinned qubits are constant → not a separate conjunct; reason: it follows from the two resource formulas
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 48, p.38

import Mathlib
import Definitions.Def_SingleInteraction_onTuple
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_Supplement_Compiler

open Matrix

namespace SingleInteraction

namespace Supplement

/-- Theorem 48 (Pinned Single-Interaction Compiler) (Hecker, *The Complexity of Single-Interaction
Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §4.1.3, p.38).

Let `A = {h(1), …, h(m)}` be `k`-qubit Hermitian interactions. For each of the two selectors there are
one interaction `h̃` and one pinned auxiliary state `|Ψancilla⟩`, depending only on `A`, such that for
every working register `W` (`NW` qubits) and every `K = Σ_{i=1}^M h(j_i)_{V_i}` with ordered tuples
`V_i` of distinct qubits and pairwise distinct pairs `(V_i, j_i)`, there are `M` ordered `k′`-tuples
`e_i` of distinct qubits of `W ⊔ A`, pairwise distinct, with `V† K̃ V = K` for
`K̃ = Σ_i h̃_{e_i}` and `V|ψ⟩ = |ψ⟩_W ⊗ |Ψancilla⟩_A`. Moreover polynomial-time computable entries of
every `h(j)` give polynomial-time computable entries of `h̃`.
1. binary selector: `k′ = k + ⌈log₂ m⌉`, `p = 2⌈log₂ m⌉`;
2. base-3 Pauli selector: `k′ = k + ⌈log₃ m⌉`, `p = 3⌈log₃ m⌉`.

**Formalization Note** `⌈log_b m⌉` is `Nat.clog b m`. The register is `Fin NW ⊕ Fin p`; `pinnedIso`
is `V`. `h̃` is also asserted Hermitian (a single interaction in the sense of Definition 31), and
`|Ψancilla⟩` normalized. The final sentence of the theorem ("if `k` and `m` are constants …") is a
consequence of the two resource formulas. -/
theorem theorem_48 (k m : ℕ) (A : Fin m → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (hA : ∀ j, (A j).IsHermitian) :
    (∃ (ht : Matrix (Fin (k + Nat.clog 2 m) → Fin 2) (Fin (k + Nat.clog 2 m) → Fin 2) ℂ)
        (Ψ : EuclideanSpace ℂ (Fin (2 * Nat.clog 2 m) → Fin 2)),
      ht.IsHermitian ∧ ‖Ψ‖ = 1 ∧ ((∀ j, EntriesPolyTime (A j)) → EntriesPolyTime ht) ∧
      ∀ (NW M : ℕ) (V : Fin M → Fin k → Fin NW) (jj : Fin M → Fin m),
        (∀ i, Function.Injective (V i)) → Function.Injective (fun i => (V i, jj i)) →
        ∃ e : Fin M → Fin (k + Nat.clog 2 m) → (Fin NW ⊕ Fin (2 * Nat.clog 2 m)),
          (∀ i, Function.Injective (e i)) ∧ Function.Injective e ∧
          (pinnedIso NW _ Ψ)ᴴ * (∑ i, onTuple ht (e i)) * pinnedIso NW _ Ψ =
            ∑ i, onTuple (A (jj i)) (V i)) ∧
    (∃ (ht : Matrix (Fin (k + Nat.clog 3 m) → Fin 2) (Fin (k + Nat.clog 3 m) → Fin 2) ℂ)
        (Ψ : EuclideanSpace ℂ (Fin (3 * Nat.clog 3 m) → Fin 2)),
      ht.IsHermitian ∧ ‖Ψ‖ = 1 ∧ ((∀ j, EntriesPolyTime (A j)) → EntriesPolyTime ht) ∧
      ∀ (NW M : ℕ) (V : Fin M → Fin k → Fin NW) (jj : Fin M → Fin m),
        (∀ i, Function.Injective (V i)) → Function.Injective (fun i => (V i, jj i)) →
        ∃ e : Fin M → Fin (k + Nat.clog 3 m) → (Fin NW ⊕ Fin (3 * Nat.clog 3 m)),
          (∀ i, Function.Injective (e i)) ∧ Function.Injective e ∧
          (pinnedIso NW _ Ψ)ᴴ * (∑ i, onTuple ht (e i)) * pinnedIso NW _ Ψ =
            ∑ i, onTuple (A (jj i)) (V i)) := by sorry

end Supplement

end SingleInteraction
