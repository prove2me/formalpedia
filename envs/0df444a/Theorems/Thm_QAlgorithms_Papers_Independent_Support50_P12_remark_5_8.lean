-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_remark_5_8
-- name    : QAlgorithms.Papers.Independent.Support50.P12.remark_5_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:41:22.125291+00:00
-- url     : https://prove2.me/theorems/837b8e69-1649-48bc-8b75-c8667aa2dc8c
-- title:
--   Remark (2-decomposable special case) 5.8
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   Assume $A^0\le B^0$, $\operatorname{Tr}\Phi(B)=\operatorname{Tr}B$, and $\Phi$ is a convex combination of two trace non-increasing maps, one two-positive and one two-copositive. Then
--
--   $$\Phi_B^*(\Phi(A))=A\quad\Longrightarrow\quad S_f(\Phi(A)\Vert\Phi(B))=S_f(A\Vert B)\quad\text{for every operator convex }f.$$
--
--   Only this expressly asserted two-decomposable special case is claimed; the wider Schwarz-decomposability question is left open.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 27, Remark (2-decomposable special case) 5.8

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

/-- Remark 5.8, PDF p.27: ONLY the asserted 2-decomposable special case;
the surrounding general decomposability question remains open. -/
theorem remark_5_8 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi)
    (hd : ∃ (t : ℝ) (Phi1 Phi2 : MatrixMap I J), t ∈ Icc 0 1 ∧
      AlgebraExtension A B Phi1 ∧ AlgebraExtension A B Phi2 ∧ AlgebraTraceNonincreasing A Phi1 ∧ AlgebraTraceNonincreasing A Phi2 ∧
      AlgebraKPositive A Phi1 2 ∧ KCoPositive A Phi2 2 ∧
      Phi = ((1 - t : ℝ) : ℂ) • Phi1 + (t : ℂ) • Phi2)
    (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A) (hXp : X.PosSemidef) (hYp : Y.PosSemidef)
    (hs : Supports X Y) (htr : tr (Phi Y) = tr Y) (hr : petz Y Phi (Phi X) = X) :
    ∀ f, DivergenceGenerator f → SemidefiniteOperatorConvex f → div f (Phi X) (Phi Y) = div f X Y := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
