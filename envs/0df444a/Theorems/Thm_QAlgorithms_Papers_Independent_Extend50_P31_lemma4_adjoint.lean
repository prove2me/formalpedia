-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma4_adjoint
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.lemma4_adjoint
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:27:04.316257+00:00
-- url     : https://prove2.me/theorems/38e51a61-0527-4bda-9e21-f1285570fc03
-- title:
--   Lemma 4: matrix representative of the Hilbert–Schmidt adjoint
-- statement:
--   Let $n>0$ and let $\Phi$ be a complex-linear endomorphism of $M_n(\mathbb C)$. Its Hilbert–Schmidt adjoint $\Phi^*$ is taken for $(X,Y)=\operatorname{Tr}(X^\dagger Y)$, and $\operatorname{mat}$ is the matrix in the matrix-unit basis. Then
--
--   $$
--   \operatorname{mat}(\Phi^*)=\operatorname{mat}(\Phi)^\dagger.
--   $$
--
--   This identifies the operator adjoint with conjugate transpose in the fixed orthonormal matrix-unit coordinates.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 7, Lemma 4: matrix representative of the Hilbert–Schmidt adjoint

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.7, Lemma 4 Eq.(20), for the Hilbert--Schmidt adjoint. -/
theorem lemma4_adjoint (n : ℕ) (hn : 0 < n) (Phi : EndMat n) :
    rowMatrixRepresentative (hsAdjoint Phi) = (rowMatrixRepresentative Phi)ᴴ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
