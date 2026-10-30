-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P10_smLemmaII1_supportedRoots
-- name    : QAlgorithms.Papers.Independent.Extend50.P10.smLemmaII1_supportedRoots
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:40:11.651007+00:00
-- url     : https://prove2.me/theorems/75f3f3b6-84e4-48c7-a59c-f8a152096d42
-- title:
--   Supplemental supported-root-space lemma
-- statement:
--   Let $D\ge1$, let $M\in M_D(\mathbb C)$ be arbitrary, let $\mathfrak d_D$ be the space of all complex diagonal matrices, and let $E_{ij}$ be the matrix units. If $I=\{(i,j):i\ne j,\ M_{ij}\ne0\}$, then
--
--   $$
--   \mathfrak d_D\oplus\bigoplus_{(i,j)\in I}\mathbb C E_{ij}\ \subseteq\ \operatorname{Lie}_{\mathbb C}(\mathfrak d_D\cup\{M\}).
--   $$
--
--   The bracket is $[A,B]=AB-BA$. This is an inclusion of the indicated sum of root spaces, without assuming that $M$ is Hermitian or connected.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, PDF p. 19, SM Lemma II.1: extract supported root spaces

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10

noncomputable section

open scoped Matrix

open QAlgorithms

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF p.19, SM Lemma II.1, the separate supplemental occurrence. -/
theorem smLemmaII1_supportedRoots (D : ℕ) (_hD : 1 ≤ D)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    Submodule.span ℂ (complexDiagonals D ∪
      {A | ∃ i j : Fin D, i ≠ j ∧ M i j ≠ 0 ∧ A = matrixUnit i j}) ≤
      generatedLie ℂ (complexDiagonals D ∪ {M}) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P10

end
