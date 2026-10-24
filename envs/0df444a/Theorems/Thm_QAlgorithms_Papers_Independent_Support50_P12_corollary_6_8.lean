-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_6_8
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_6_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:46:41.312357+00:00
-- url     : https://prove2.me/theorems/a0f0e409-b693-4b5f-ad4d-8d146a5c5d65
-- title:
--   Corollary 6.8
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   If $\mathcal A$ contains three pairwise orthogonal nonzero projections, there is no operator convex admissible $f$ with $|\operatorname{supp}\mu_f|\ge6$ and strictly increasing $g$ on its attained extended range such that
--
--   $$C(\rho\Vert\sigma)=g(S_f(\rho\Vert\sigma))\quad\text{for all density pairs in }\mathcal A.$$
--
--   The hypothesis concerns projections of the algebra, not merely ambient dimension.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 31, Corollary 6.8

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

/-- Corollary 6.8, PDF p.31: three orthogonal NONZERO projections, allowing
arbitrary representation multiplicities. -/
theorem corollary_6_8 [Nonempty I] (A : Alg I)
    (ha : ∃ P : Fin 3 → Mat I, (∀ i, P i ∈ A ∧ (P i).IsHermitian ∧ P i * P i = P i ∧ P i ≠ 0) ∧
      ∀ i j, i ≠ j → P i * P j = 0) :
    ¬ ∃ f, DivergenceGenerator f ∧ SemidefiniteOperatorConvex f ∧ Rich f 6 ∧ MonotoneRepresentation A chernoff f := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
