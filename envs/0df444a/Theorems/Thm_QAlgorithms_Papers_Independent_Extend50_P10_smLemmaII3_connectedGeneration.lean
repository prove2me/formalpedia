-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P10_smLemmaII3_connectedGeneration
-- name    : QAlgorithms.Papers.Independent.Extend50.P10.smLemmaII3_connectedGeneration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:41:12.685804+00:00
-- url     : https://prove2.me/theorems/3f8e4474-b8bf-4a45-84c1-55d653b22b83
-- title:
--   Supplemental complex and real connected-generation lemma
-- statement:
--   Let $D\ge1$ and let $H\in M_D(\mathbb C)$ be Hermitian. Its index graph, with an edge between distinct indices $i,j$ whenever $H_{ij}\ne0$, is assumed connected. Write $\mathfrak d_D$ for all complex diagonal matrices and $\mathfrak d_{\mathbb R,D}$ for all real diagonal matrices. Then
--
--   $$
--   \operatorname{Lie}_{\mathbb C}(\mathfrak d_D\cup\{H\})=\mathfrak{gl}(D,\mathbb C),\qquad
--   \operatorname{Lie}_{\mathbb R}(i\mathfrak d_{\mathbb R,D}\cup\{iH\})=\mathfrak u(D).
--   $$
--
--   Here $\mathfrak u(D)=\{A:A^\dagger=-A\}$. The result describes both the complex generated algebra and its real unitary form, including the singleton case.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, PDF p. 21, SM Lemma II.3: connected Hamiltonian generates both Lie algebras

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10

noncomputable section

open scoped Matrix

open QAlgorithms

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF p.21, SM Lemma II.3, including both complex and real conclusions. -/
theorem smLemmaII3_connectedGeneration (D : ℕ) (_hD : 1 ≤ D)
    (H : Matrix (Fin D) (Fin D) ℂ) (hH : PathConnectedHamiltonian H) :
    generatedLie ℂ (complexDiagonals D ∪ {H}) = ⊤ ∧
    ∀ A : Matrix (Fin D) (Fin D) ℂ,
      A ∈ generatedLie ℝ (imaginaryRealDiagonals D ∪ {Complex.I • H}) ↔
        A.conjTranspose = -A := by sorry

end QAlgorithms.Papers.Independent.Extend50.P10

end
