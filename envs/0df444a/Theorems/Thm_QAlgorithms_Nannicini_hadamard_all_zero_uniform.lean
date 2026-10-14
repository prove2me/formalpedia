-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_hadamard_all_zero_uniform
-- name    : QAlgorithms.Nannicini.hadamard_all_zero_uniform
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:51:41.00815+00:00
-- url     : https://prove2.me/theorems/82b92ddf-f4ff-4da8-b99d-27a3b9e83128
-- title:
--   Hadamard on every qubit of |0⟩ gives the uniform superposition
-- statement:
--   Let $q\ge 0$ and let $H=\frac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ be the Hadamard gate. Consider a $q$-qubit register in the all-zero basis state $|\vec 0\rangle_q$.
--
--   1. Applying $H$ to each of the $q$ qubits, one after the other, yields the uniform superposition.
--   2. Applying the $2^q\times 2^q$ matrix $H^{\otimes q}$, whose entries are $(H^{\otimes q})_{\vec k,\vec x}=2^{-q/2}(-1)^{\vec k\bullet\vec x}$ (Eq. (1.5)), also yields the uniform superposition:
--
--   $$
--   H^{\otimes q}|\vec 0\rangle_q=\frac{1}{\sqrt{2^q}}\sum_{\vec\jmath\in\{0,1\}^q}|\vec\jmath\rangle .
--   $$
--
--   This is how many quantum algorithms start: $q$ gates turn the initial state into an equal-weight superposition of all $2^q$ basis states.
--
--   **Formalization Note** Applying $H$ to qubit $i$ is the embedding of the one-qubit matrix $H$ on wire $i$; the product over all wires is taken in wire order (the factors commute). The uniform superposition is the vector all of whose amplitudes equal $1/\sqrt{2^q}$. The case $q=0$ is included; both sides are then the one-dimensional unit vector.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 25, Proposition 1.38. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms

/-- Nannicini, Proposition 1.38, PDF p. 25. Given a `q`-qubit register in the state `|0⟩_q`,
applying the Hadamard gate to all qubits, or equivalently the matrix `H^{⊗q}` (Eq. (1.5)),
yields the uniform superposition `(1/√(2^q)) Σ_{j ∈ {0,1}^q} |j⟩`.

The first conjunct applies `H` to each wire in turn (wire `0` first); the second applies the
frozen `hadamardN q`, the matrix of Eq. (1.5). `uniformState (Qubits q)` has every amplitude
equal to `1/√(card (Qubits q)) = 1/√(2^q)`. -/
theorem hadamard_all_zero_uniform (q : ℕ) :
    act (orderedProd fun i : Fin q =>
        embedOp (Gate.ofMatrix1 hadamard).mat (Stabilizer.wire1 i)) (zeroKet q) =
      uniformState (Qubits q) ∧
    act (hadamardN q) (zeroKet q) = uniformState (Qubits q) := by
  sorry




end QAlgorithms.Nannicini
