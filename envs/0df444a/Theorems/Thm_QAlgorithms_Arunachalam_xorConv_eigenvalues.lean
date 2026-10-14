-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_xorConv_eigenvalues
-- name    : QAlgorithms.Arunachalam.xorConv_eigenvalues
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:56:43.233991+00:00
-- url     : https://prove2.me/theorems/118d34ba-be92-444e-9697-99d260372d93
-- title:
--   Eigenvalues of an XOR-convolution matrix are scaled Fourier coefficients
-- statement:
--   Let $g:\{0,1\}^k\to\mathbb R$ and let $P\in\mathbb R^{2^k\times2^k}$ be defined by $P(x,y)=g(x+y)$, where addition is over $\mathbb F_2$. Write $\hat g(Q)=\mathbb E_{z\in\{0,1\}^k}[g(z)(-1)^{Q\cdot z}]$ for the Fourier coefficients of $g$. Then the eigenvalues of $P$, counted with multiplicity, are $2^k\hat g(Q)$ for $Q\in\{0,1\}^k$:
--
--   $$
--   \chi_P(X)=\prod_{Q\in\{0,1\}^k}\bigl(X-2^k\hat g(Q)\bigr),\qquad \operatorname{spec}(P)=\{2^k\hat g(Q):Q\in\{0,1\}^k\}.
--   $$
--
--   The Hadamard matrix diagonalizes every such matrix; this is the basic tool for computing the square root of the Gram matrix in Theorem 7.5.1.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 171, Claim 7.5.2. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning



/-- Arunachalam p.171, Claim 7.5.2: for `g : {0,1}^k → ℝ` and `P ∈ ℝ^{2^k × 2^k}` defined by
`P(x, y) = g(x + y)` (addition over `F₂`), the eigenvalues of `P` are
`{2^k ĝ(Q) : Q ∈ {0,1}^k}`, with `ĝ(Q) = E_z[g(z)(−1)^{Q·z}]`.

Stated with multiplicities, as the proof gives it (`H P H⁻¹ = diag(2^k ĝ(Q))`): the
characteristic polynomial of `P` is `∏_Q (X − 2^k ĝ(Q))`; and, as a set, the spectrum of `P` is
`{2^k ĝ(Q)}`. -/
theorem xorConv_eigenvalues {k : ℕ} (g : (Fin k → ZMod 2) → ℝ) :
    (xorConvMatrix g).charpoly =
        ∏ Q : Fin k → ZMod 2, (Polynomial.X - Polynomial.C ((2 : ℝ) ^ k * boolFourier g Q)) ∧
      spectrum ℝ (xorConvMatrix g) = Set.range fun Q => (2 : ℝ) ^ k * boolFourier g Q := by
  sorry




end QAlgorithms.Arunachalam
