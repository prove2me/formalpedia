-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_blockEncoding_mul
-- name    : QAlgorithms.Nannicini.blockEncoding_mul
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:52:09.131459+00:00
-- url     : https://prove2.me/theorems/8ca4cb11-8f80-4398-bfcb-69cc0fbda11d
-- title:
--   Product of block-encodings (error term corrected)
-- statement:
--   A $(q+a)$-qubit unitary $U$ is an $(\alpha, a, \xi)$-block-encoding of a $q$-qubit operator $A$ if
--
--   $$
--   \bigl\| \alpha\,(\langle 0|_a \otimes I)\,U\,(|0\rangle_a \otimes I) - A \bigr\| \le \xi,
--   $$
--
--   where the auxiliary register comes first and $\|\cdot\|$ is the operator norm.
--
--   Let $U_A$ be an $(\alpha, a, \xi_A)$-block-encoding of $A$ and $U_B$ a $(\beta, b, \xi_B)$-block-encoding of $B$, both $q$-qubit operators, with $\alpha, \beta \ge 0$. Order the registers as $|\cdot\rangle_a|\cdot\rangle_b|\cdot\rangle_q$. Let $I_b \otimes U_A$ act as $U_A$ on registers $a$ and $q$ and as the identity on $b$, and let $I_a \otimes U_B$ act as $U_B$ on registers $b$ and $q$ and as the identity on $a$. Then
--
--   $$
--   (I_b \otimes U_A)(I_a \otimes U_B) \text{ is an } (\alpha\beta,\; a+b,\; \alpha\xi_B + \beta\xi_A + \xi_A\xi_B)\text{-block-encoding of } AB,
--   $$
--
--   with auxiliary register $|\cdot\rangle_a|\cdot\rangle_b$.
--
--   Together with linear combinations, products of block-encodings let one implement polynomials of block-encoded matrices.
--
--   **Correction.** The source prints the error $\alpha\xi_B + \beta\xi_A$. That is false: with $q=a=b=0$, $U_A=U_B=1$, $\alpha=\beta=1$, $A = 1+\xi_A$ and $B = 1+\xi_B$, the error is $\xi_A+\xi_B+\xi_A\xi_B$. The extra term $\xi_A\xi_B$ is what the definition yields.
--
--   **Formalization Note** The auxiliary register of the product is the pair type $\{0,1\}^a \times \{0,1\}^b$ with zero state $(0,0)$, rather than one $(a+b)$-bit string. Being a block-encoding includes unitarity.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 160, Proposition 7.14. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Nannicini_Ch07a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini


/-- Nannicini Proposition 7.14 (p.160), product of block-encodings, with the error term
corrected.

If `U_A` is an `(α, a, ξ_A)`-block-encoding of the `q`-qubit operator `A` and `U_B` a
`(β, b, ξ_B)`-block-encoding of `B`, then on the registers `|·⟩_a |·⟩_b |·⟩_q` (Rem. 7.15) the
unitary `(I_b ⊗ U_A)(I_a ⊗ U_B)` is an `(αβ, a + b, αξ_B + βξ_A + ξ_Aξ_B)`-block-encoding of `AB`.
Here `I_b ⊗ U_A` acts as `U_A` on registers `a, q` and as the identity on `b`, and `I_a ⊗ U_B`
acts as `U_B` on registers `b, q` and as the identity on `a`.

**Correction (trap 30).** The source prints the error `αξ_B + βξ_A`, which is false: with
`q = a = b = 0`, `U_A = U_B = 1`, `α = β = 1`, `A = 1 + ξ_A`, `B = 1 + ξ_B` the error of `AB` is
`ξ_A + ξ_B + ξ_Aξ_B`. The source's proof gives `α‖Ã‖ξ_B + ξ_A‖B‖ ≤ αξ_B + ξ_A(β + ξ_B)`.
The subnormalization factors are nonnegative (`0 ≤ α`, `0 ≤ β`), as the source's "scaled-down"
reading of Def. 7.10 assumes. -/
theorem blockEncoding_mul {q a b : ℕ}
    (UA : Matrix (Qubits a × Qubits q) (Qubits a × Qubits q) ℂ)
    (UB : Matrix (Qubits b × Qubits q) (Qubits b × Qubits q) ℂ)
    (A B : Matrix (Qubits q) (Qubits q) ℂ) (α β ξA ξB : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : IsBlockEncoding (fun _ => false) UA α ξA A)
    (hB : IsBlockEncoding (fun _ => false) UB β ξB B) :
    IsBlockEncoding ((fun _ => false, fun _ => false) : Qubits a × Qubits b)
      ((Matrix.of fun y z : (Qubits a × Qubits b) × Qubits q =>
          if y.1.2 = z.1.2 then UA (y.1.1, y.2) (z.1.1, z.2) else 0) *
        (Matrix.of fun y z : (Qubits a × Qubits b) × Qubits q =>
          if y.1.1 = z.1.1 then UB (y.1.2, y.2) (z.1.2, z.2) else 0))
      (α * β) (α * ξB + β * ξA + ξA * ξB) (A * B) := by
  sorry














end QAlgorithms.Nannicini
