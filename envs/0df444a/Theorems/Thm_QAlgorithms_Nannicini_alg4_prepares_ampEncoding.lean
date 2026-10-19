-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_alg4_prepares_ampEncoding
-- name    : QAlgorithms.Nannicini.alg4_prepares_ampEncoding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:46:46.553673+00:00
-- url     : https://prove2.me/theorems/c34e52d6-2d45-4775-a440-edb5f945ffdc
-- title:
--   Algorithm 4 (binary tree of controlled R_Y rotations) prepares the amplitude encoding of a real unit vector
-- statement:
--   Let $n \ge 1$, $d = 2^n$, and let $x \in \mathbb{R}^d$ with $\|x\| = 1$. Index the entries of $x$ by $j \in \{0, \dots, d-1\}$ and identify $j$ with the $n$-bit string $\vec\jmath$ that is its binary expansion, most significant bit on the first qubit. The binary tree of $x$ has node values
--
--   $$
--   N(k, j) = \sum_{i \,:\, \lfloor i / 2^{n-k} \rfloor = j} x_i^2, \qquad 0 \le k \le n,\ 0 \le j < 2^k,
--   $$
--
--   and $R_Y(\theta) = \begin{pmatrix} \cos(\theta/2) & -\sin(\theta/2) \\ \sin(\theta/2) & \cos(\theta/2) \end{pmatrix}$. Algorithm 4 first rotates qubit 1 by $R_Y(\theta_{0,0})$; then, for $k = 1, \dots, n-1$, it applies to qubit $k+1$ the rotation $R_Y(\theta_{k,j})$ controlled on the first $k$ qubits being in state $|\vec\jmath\rangle$, where
--
--   $$
--   \theta_{k,j} = 2 \arccos \sqrt{\frac{N(k+1, 2j)}{N(k+1, 2j) + N(k+1, 2j+1)}};
--   $$
--
--   finally it applies the diagonal operator $\sum_j \operatorname{sign}(x_j) |\vec\jmath\rangle\langle\vec\jmath|$ with $\operatorname{sign}(x_j) = -1$ if $x_j < 0$ and $+1$ otherwise. Let $U_x$ be the resulting operator on $n$ qubits. Then $U_x$ is unitary and
--
--   $$
--   U_x |0 \cdots 0\rangle = |\mathrm{amp}(x)\rangle = \sum_{j=0}^{d-1} \frac{x_j}{\|x\|} |\vec\jmath\rangle.
--   $$
--
--   This is the Grover–Rudolph style construction of the amplitude encoding, used as the state-preparation subroutine for classical vectors throughout the book.
--
--   **Formalization Note** The operator is the shared definition `alg4Unitary`; the rotation of qubit 1 is the step with $k = 0$ (no controls). When $N(k+1,2j) + N(k+1,2j+1) = 0$ the angle formula divides by zero (Lean's value is $2\arccos 0 = \pi$); that branch carries amplitude zero, and the operator is still unitary. The value $\operatorname{sign}(0) = +1$ is used because a zero sign would not be unitary; that amplitude is zero anyway.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 125, Proposition 5.36. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05c_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- Nannicini p.125, Proposition 5.36: "Alg. 4 returns a quantum circuit on n qubits mapping
`|0⟩` to `|amp(x)⟩`."

Standing assumptions of §5.2 (p.124) and Alg. 4 (p.126): `d = 2^n`, `x ∈ ℝ^d` with `‖x‖ = 1`;
`n ≥ 1` because the initialization (line 2) reads the level-1 nodes `N(1, 0)`, `N(1, 1)` of the
tree. The conclusion: the operator produced by Alg. 4 is unitary (a quantum circuit) and maps
`|0…0⟩` to `|amp(x)⟩`. -/
theorem alg4_prepares_ampEncoding (n : ℕ) (hn : 1 ≤ n) (x : Fin (2 ^ n) → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) :
    alg4Unitary n x ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧
      act (alg4Unitary n x) (zeroKet n) =
        padState n (normalizedVec (WithLp.toLp 2 fun j => (x j : ℂ))) := by
  sorry












end QAlgorithms.Nannicini
