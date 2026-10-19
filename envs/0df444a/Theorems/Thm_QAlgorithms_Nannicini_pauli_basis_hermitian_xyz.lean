-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_pauli_basis_hermitian_xyz
-- name    : QAlgorithms.Nannicini.pauli_basis_hermitian_xyz
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:51:14.667004+00:00
-- url     : https://prove2.me/theorems/3879c9ce-882a-49e1-b9f0-73894f587495
-- title:
--   Pauli matrices: a Hermitian basis of C^{2×2} with XYZ = iI
-- statement:
--   Let the Pauli gates be (Def. 1.36)
--
--   $$
--   I=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\quad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
--   $$
--
--   Then:
--
--   1. $I,X,Y,Z$ form a basis of the complex vector space $\mathbb C^{2\times 2}$ (they are linearly independent over $\mathbb C$ and span it);
--   2. each of $I,X,Y,Z$ is Hermitian;
--   3. $XYZ=iI$.
--
--   The Pauli matrices are the basic single-qubit gates, and this basis property lets any single-qubit operator be expanded in them.
--
--   **Formalization Note** Matrices are indexed by $\{0,1\}$ with $0$ the first row and column; the extracted text garbles $I$, which is the identity in the source.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 24, Proposition 1.37. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

namespace QAlgorithms.Nannicini





/-- Nannicini p.24, Proposition 1.37: the four Pauli gates `I, X, Y, Z` (Def. 1.36) form a basis
of `ℂ^{2×2}`, each is Hermitian, and `XYZ = iI`. -/
theorem pauli_basis_hermitian_xyz :
    LinearIndependent ℂ ![(1 : Matrix Bool Bool ℂ), pauliX, pauliY, pauliZ] ∧
    Submodule.span ℂ (Set.range ![(1 : Matrix Bool Bool ℂ), pauliX, pauliY, pauliZ]) = ⊤ ∧
    (1 : Matrix Bool Bool ℂ).IsHermitian ∧ pauliX.IsHermitian ∧ pauliY.IsHermitian ∧
    pauliZ.IsHermitian ∧
    pauliX * pauliY * pauliZ = Complex.I • (1 : Matrix Bool Bool ℂ) := by
  sorry

end QAlgorithms.Nannicini
