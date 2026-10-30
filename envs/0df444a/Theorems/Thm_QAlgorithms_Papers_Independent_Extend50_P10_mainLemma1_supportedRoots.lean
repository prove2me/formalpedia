-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P10_mainLemma1_supportedRoots
-- name    : QAlgorithms.Papers.Independent.Extend50.P10.mainLemma1_supportedRoots
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:35:43.347282+00:00
-- url     : https://prove2.me/theorems/bf61fd7c-5799-4b5e-ae70-e13bf1d87e87
-- title:
--   Supported root spaces from diagonal controls
-- statement:
--   Let $D\ge1$, let $M\in M_D(\mathbb C)$ be arbitrary, let $\mathfrak d_D$ be the space of all complex diagonal matrices, and let $E_{ij}$ be the matrix units. If $I=\{(i,j):i\ne j,\ M_{ij}\ne0\}$, then
--
--   $$
--   \mathfrak d_D\oplus\bigoplus_{(i,j)\in I}\mathbb C E_{ij}\ \subseteq\ \operatorname{Lie}_{\mathbb C}(\mathfrak d_D\cup\{M\}).
--   $$
--
--   The bracket is $[A,B]=AB-BA$. This is an inclusion of the indicated sum of root spaces, without assuming that $M$ is Hermitian or connected.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, PDF p. 6, Main Lemma 1: extract the supported root spaces

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10

noncomputable section

open scoped Matrix

open QAlgorithms

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Main Lemma 1: the sum of the diagonal space and exactly the supported
one-dimensional off-diagonal root spaces is contained in the generated complex
Lie algebra. No Hermiticity or connectedness assumption is made on M. -/
theorem mainLemma1_supportedRoots (D : ℕ) (_hD : 1 ≤ D)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    Submodule.span ℂ (complexDiagonals D ∪
      {A | ∃ i j : Fin D, i ≠ j ∧ M i j ≠ 0 ∧ A = matrixUnit i j}) ≤
      generatedLie ℂ (complexDiagonals D ∪ {M}) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P10

end
