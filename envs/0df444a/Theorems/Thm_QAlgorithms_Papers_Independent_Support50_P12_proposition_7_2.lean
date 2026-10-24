-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_proposition_7_2
-- name    : QAlgorithms.Papers.Independent.Support50.P12.proposition_7_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:49:02.802607+00:00
-- url     : https://prove2.me/theorems/f9669672-ca5b-480f-ac27-3505525955ed
-- title:
--   Proposition 7.2
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   Let $\Phi$ be trace preserving and two-positive. Let $C$ be a nonempty code of density operators, and let another density set $C_0$ have the same closed convex hull. Fix one density operator $\sigma$ covering the support of $C$. Put
--
--   $$m=\inf_{\rho\in C_0}\{-\psi_{\Phi(\rho),\Phi(\sigma)}(0)-\psi\prime_{\Phi(\rho),\Phi(\sigma)}(0)\}.$$
--
--   If one rate satisfies $0<r<m$ and $H_r(\Phi(\rho)\Vert\Phi(\sigma))=H_r(\rho\Vert\sigma)$ for every $\rho\in C_0$, then $\Phi_\sigma^*(\Phi(\rho))=\rho$ for every $\rho$ in the closed convex hull of $C$. The infimum is extended and taken over exactly $C_0$, with no attainment assumption. Nonorthogonality guards the derivative and follows from the state/support setting.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 35, Proposition 7.2

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

/-- Proposition 7.2, PDF p.35: one rate lies strictly below the ACTUAL infimum
on exactly C0, with no attainment or pointwise-only replacement. -/
theorem proposition_7_2 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hc : AlgebraExtension A B Phi) (ht : AlgebraTracePreserving A Phi) (h2 : AlgebraKPositive A Phi 2)
    (C C0 : Set (Mat I)) (hn : C.Nonempty) (hC : ∀ rho ∈ C, AlgebraDensity A rho)
    (hC0 : ∀ rho ∈ C0, AlgebraDensity A rho) (hh : hull C0 = hull C)
    (sigma : Mat I) (hs : AlgebraDensity A sigma) (hcover : Covers C sigma)
    (hoverlap : ∀ rho ∈ C0, 0 < tr (supp (Phi rho) * supp (Phi sigma)))
    (r : ℝ) (hr : 0 < r)
    (hm : (r : EReal) < sInf {v : EReal | ∃ rho ∈ C0,
      v = ((-psiReal (Phi rho) (Phi sigma) 0 - deriv (psiReal (Phi rho) (Phi sigma)) 0 : ℝ) : EReal)})
    (heq : ∀ rho ∈ C0, hoeffding (Phi rho) (Phi sigma) r = hoeffding rho sigma r) :
    ∀ rho ∈ hull C, petz sigma Phi (Phi rho) = rho := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
