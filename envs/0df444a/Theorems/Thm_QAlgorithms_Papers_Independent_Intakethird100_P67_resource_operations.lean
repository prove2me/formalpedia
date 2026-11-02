-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_resource_operations
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.resource_operations
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:03:35.806216+00:00
-- url     : https://prove2.me/theorems/d1a9727b-e54b-4efb-870a-3ef22432cf4a
-- title:
--   §V B: required elementary operations and free-unitary symmetry
-- statement:
--   Suppose all system and sample registers carry the same unitary group representation $R(g)$ or the same intrinsic Hermitian Hamiltonian $H$, while ancillary controls carry the trivial representation or zero Hamiltonian. Let $S^{cc}$ be the full-register SWAP controlled by two ancillary qubits. Then
--
--   $$[S^{cc},R(g)\otimes R(g)\otimes I_{\rm anc}]=0,\qquad[S^{cc},(H\otimes I+I\otimes H)\otimes I_{\rm anc}]=0.$$
--
--   Ancillary unitaries commute with the extended symmetry action, and every ancillary density is invariant under the trivial ancillary symmetry. Thus the required register operations are symmetric or energy conserving under the stated extension. This operational observation does not assert that pure zero-Hamiltonian states are thermodynamically free, nor does it supply a symmetry-sector or Lie-algebra decomposition.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 11, §V B: required elementary operations and free-unitary symmetry

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.11, Section V B: all required full-register SWAPs and ancillary unitaries
commute with identical on-site symmetry actions or the total intrinsic Hamiltonian.
This asserts no thermodynamic freeness for arbitrary pure auxiliary states. -/
theorem resource_operations {G : Type*} [Group G] (R : G →* Matrix.unitaryGroup I ℂ)
    (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    (∀ g : G, doubleControlledSwap * Matrix.kronecker
      (Matrix.kronecker (R g : Matrix I I ℂ) (R g : Matrix I I ℂ)) (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      Matrix.kronecker (Matrix.kronecker (R g : Matrix I I ℂ) (R g : Matrix I I ℂ))
        (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) * doubleControlledSwap) ∧
    (doubleControlledSwap * Matrix.kronecker
      (Matrix.kronecker H (1 : Matrix I I ℂ) + Matrix.kronecker (1 : Matrix I I ℂ) H) (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      Matrix.kronecker (Matrix.kronecker H (1 : Matrix I I ℂ) + Matrix.kronecker (1 : Matrix I I ℂ) H)
        (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) * doubleControlledSwap) ∧
    (∀ (V : Matrix.unitaryGroup (Bool × Bool) ℂ) (g : G),
      Matrix.kronecker (1 : Matrix (I × I) (I × I) ℂ) (V : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        Matrix.kronecker (Matrix.kronecker (R g : Matrix I I ℂ) (R g : Matrix I I ℂ)) (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      Matrix.kronecker (Matrix.kronecker (R g : Matrix I I ℂ) (R g : Matrix I I ℂ)) (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        Matrix.kronecker (1 : Matrix (I × I) (I × I) ℂ) (V : Matrix (Bool × Bool) (Bool × Bool) ℂ)) ∧
    (∀ V : Matrix.unitaryGroup (Bool × Bool) ℂ,
      Matrix.kronecker (1 : Matrix (I × I) (I × I) ℂ) (V : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        Matrix.kronecker (Matrix.kronecker H (1 : Matrix I I ℂ) + Matrix.kronecker (1 : Matrix I I ℂ) H)
          (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      Matrix.kronecker (Matrix.kronecker H (1 : Matrix I I ℂ) + Matrix.kronecker (1 : Matrix I I ℂ) H)
        (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) * Matrix.kronecker (1 : Matrix (I × I) (I × I) ℂ) (V : Matrix (Bool × Bool) (Bool × Bool) ℂ)) ∧
    (∀ sigma : Matrix (Bool × Bool) (Bool × Bool) ℂ, IsDensityMatrix sigma → densityConjugation 1 sigma = sigma) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
