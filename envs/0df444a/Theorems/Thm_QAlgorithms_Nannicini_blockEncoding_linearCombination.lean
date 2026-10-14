-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_blockEncoding_linearCombination
-- name    : QAlgorithms.Nannicini.blockEncoding_linearCombination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:13.44286+00:00
-- url     : https://prove2.me/theorems/87c06d52-6e2b-4614-a13b-4b13bfe67290
-- title:
--   Linear combination of block-encodings (error term corrected for α < 1)
-- statement:
--   Let $A = \sum_{j=0}^{m-1} y_j A^{(j)}$ be a $q$-qubit operator with coefficients $y \in \mathbb{C}^m$. A pair of $p$-qubit unitaries $(P_L, P_R)$ is a $(\beta, p, \xi_1)$-state-preparation pair for $y$ if $\|y\|_1 \le \beta$, $m \le 2^p$, and, writing $P_L|0\rangle = \sum_j c_j |j\rangle$ and $P_R|0\rangle = \sum_j d_j|j\rangle$,
--
--   $$
--   \sum_{j=0}^{m-1} \bigl|\beta\,\bar c_j d_j - y_j\bigr| \le \xi_1, \qquad \bar c_j d_j = 0 \ (j \ge m).
--   $$
--
--   For each $j < m$ let $U^{(j)}$ be an $(\alpha, a, \xi_2)$-block-encoding of $A^{(j)}$, with $\alpha \ge 0$ and $\xi_2 \ge 0$. On the registers $|\cdot\rangle_p|\cdot\rangle_a|\cdot\rangle_q$ let
--
--   $$
--   V = \sum_{j \le m-1} |j\rangle\langle j| \otimes U^{(j)} + \Bigl(I_p - \sum_{j \le m-1}|j\rangle\langle j|\Bigr)\otimes I_a \otimes I_q ,
--   $$
--
--   where a $p$-bit string $j$ is read as an integer with the most significant bit first. Then
--
--   $$
--   (P_L^\dagger \otimes I_{a+q})\, V\, (P_R \otimes I_{a+q}) \text{ is an } \bigl(\alpha\beta,\; a+p,\; \alpha\xi_1 + \max(\alpha,1)\,\beta\,\xi_2\bigr)\text{-block-encoding of } A,
--   $$
--
--   with auxiliary register $|\cdot\rangle_p|\cdot\rangle_a$. This circuit uses $V$, $P_R$ and $P_L^\dagger$ once each.
--
--   With products of block-encodings, this gives block-encodings of polynomials in a block-encoded matrix, the basis of Hamiltonian simulation and matrix functions in this framework.
--
--   **Correction.** The source prints the error $\alpha\xi_1 + \alpha\beta\xi_2$. For $\alpha \ge 1$ the stated error is exactly that. For $\alpha < 1$ the printed bound is false: with $m=1$, $p=a=0$, $P_L=P_R=1$, $y_0=\beta$, $U^{(0)}=1$ and $A^{(0)} = \alpha + E$ with $\|E\| = \xi_2$, the error is $\beta\xi_2$.
--
--   **Formalization Note** The auxiliary register is the pair type $\{0,1\}^p \times \{0,1\}^a$ with zero state $(0,0)$. $V$ is built from the $U^{(j)}$ as displayed. "Implement with a single use" is rendered by stating that this specific product is the block-encoding.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 161, Proposition 7.18. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Nannicini_Ch07a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini



/-- Nannicini Proposition 7.18 (pp.161–162), linear combination of block-encodings, with the
error term corrected for `α < 1`.

Let `A = ∑_{j=0}^{m−1} y_j A^(j)` be a `q`-qubit operator, `(P_L, P_R)` a
`(β, p, ξ₁)`-state-preparation pair for `y` (Def. 7.16), and `U^(j)` an
`(α, a, ξ₂)`-block-encoding of `A^(j)` for each `j < m`. Let
`V = ∑_{j ≤ m−1} |j⟩⟨j| ⊗ U^(j) + (I_p − ∑_{j ≤ m−1} |j⟩⟨j|) ⊗ I_a ⊗ I_q` on the registers
`|·⟩_p |·⟩_a |·⟩_q` (the index `j` of a `p`-bit string is `bitsToNat`, most significant bit
first). Then `(P_L† ⊗ I_{a+q}) V (P_R ⊗ I_{a+q})` (the circuit of the proof, p.162, using `V`,
`P_R` and `P_L†` once each) is an `(αβ, a + p, αξ₁ + max(α, 1)·βξ₂)`-block-encoding of `A`,
with auxiliary register `|·⟩_p |·⟩_a`.

**Correction (trap 30).** The source prints the error `αξ₁ + αβξ₂`; for `α ≥ 1` the stated
error is exactly that. For `α < 1` the printed bound is false: with `m = 1`, `p = a = 0`,
`P_L = P_R = 1`, `y_0 = β`, `U^(0) = 1` and `A^(0) = α·1 + E`, `‖E‖ = ξ₂`, the error is
`βξ₂ > αβξ₂`. The source's proof gives `αξ₁ + ‖y‖₁ξ₂ ≤ αξ₁ + βξ₂`. The subnormalization `α`
and the error `ξ₂` are nonnegative (with `m = 0` nothing else forces `0 ≤ ξ₂`). -/
theorem blockEncoding_linearCombination {q a p m : ℕ}
    (Aj : Fin m → Matrix (Qubits q) (Qubits q) ℂ) (y : Fin m → ℂ) (β ξ₁ : ℝ)
    (PL PR : Matrix (Qubits p) (Qubits p) ℂ) (hP : IsStatePrepPair β ξ₁ y PL PR)
    (U : Fin m → Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ) (α ξ₂ : ℝ)
    (hα : 0 ≤ α) (hξ₂ : 0 ≤ ξ₂)
    (hU : ∀ j, IsBlockEncoding (fun _ => false) (U j) α ξ₂ (Aj j)) :
    IsBlockEncoding ((fun _ => false, fun _ => false) : Qubits p × Qubits a)
      (Matrix.kronecker (Matrix.kronecker (star PL) (1 : Matrix (Qubits a) (Qubits a) ℂ))
          (1 : Matrix (Qubits q) (Qubits q) ℂ) *
        (Matrix.of fun u v : (Qubits p × Qubits a) × Qubits q =>
          if u.1.1 = v.1.1 then
            (if h : bitsToNat u.1.1 < m then U ⟨bitsToNat u.1.1, h⟩ (u.1.2, u.2) (v.1.2, v.2)
              else (1 : Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ) (u.1.2, u.2)
                (v.1.2, v.2))
          else 0) *
        Matrix.kronecker (Matrix.kronecker PR (1 : Matrix (Qubits a) (Qubits a) ℂ))
          (1 : Matrix (Qubits q) (Qubits q) ℂ))
      (α * β) (α * ξ₁ + max α 1 * β * ξ₂) (∑ j, y j • Aj j) := by
  sorry













end QAlgorithms.Nannicini
