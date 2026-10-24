-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_lemma_3_11
-- name    : QAlgorithms.Papers.Independent.Support50.P12.lemma_3_11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:30:31.450334+00:00
-- url     : https://prove2.me/theorems/3410689f-e3bd-4058-a41a-84b3903505b7
-- title:
--   Lemma 3.11
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   Assume $B
--   e0$, $\Phi$ is trace non-increasing and two-positive, and $\operatorname{Tr}\Phi(B)=\operatorname{Tr}B$. There are shared orthogonal decompositions $\operatorname{supp}B_m=\bigoplus_k H_{m,k,L}\otimes H_{m,k,R}$, where $B_1=B$, $B_2=\Phi(B)$, invertible right density operators $\omega_k,\widetilde\omega_k$, and unitaries $U_k:H_{1,k,L}\to H_{2,k,L}$ such that
--
--   $$\ker(\mathrm{id}-\Phi_B^*\Phi)_+=\bigoplus_k B(H_{1,k,L})_+\otimes\omega_k,$$
--
--   $$\Phi(X\otimes\omega_k)=U_kXU_k^*\otimes\widetilde\omega_k\quad(X\in B(H_{1,k,L})).$$
--
--   All blocks lie in the stated algebras, and the same data describe the entire positive fixed cone. Neither cone equality nor the action formula is assumed as input data.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 15, Lemma 3.11

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Lemma 3.11, PDF pp.15–16: one shared decomposition for the ENTIRE positive
fixed cone, with the block action formula as a conclusion. -/
theorem lemma_3_11 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : AlgebraKPositive A Phi 2) (ht : AlgebraTraceNonincreasing A Phi)
    (Y : Mat I) (hY : Y ∈ A) (hYp : Y.PosSemidef) (hn : Y ≠ 0) (htr : tr (Phi Y) = tr Y) :
    ∃ D : RecoveryBlocks I J, BlockSupports D {Y} {Phi Y} ∧
      (∀ X ∈ A, (X.PosSemidef ∧ petz Y Phi (Phi X) = X) ↔
        ∃ Z : ∀ k, Mat (Fin (D.left1 k)), (∀ k, (Z k).PosSemidef) ∧
          X = ∑ k, inputBlock D k (Z k)) ∧
      (∀ k X, inputBlock D k X ∈ A ∧ Phi (inputBlock D k X) = outputBlock D k X) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
