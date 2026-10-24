-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_proposition_6_4
-- name    : QAlgorithms.Papers.Independent.Support50.P12.proposition_6_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:43:36.076476+00:00
-- url     : https://prove2.me/theorems/17d1c0b6-7f6a-4092-becd-0b7f3aaa790d
-- title:
--   Proposition 6.4
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized. Write $S_\alpha(A\Vert B)$ for the unnormalized Petz Rényi entropy, $\psi_{A,B}(\alpha)=\log\operatorname{Tr}A^\alpha B^{1-\alpha}$, $C(A\Vert B)=\sup_{0\le\alpha<1}-\psi_{A,B}(\alpha)$, and $H_r(A\Vert B)=\sup_{0\le\alpha<1}[-\alpha r-\psi_{A,B}(\alpha)]/(1-\alpha)$. Logarithms are natural and $\log0=-\infty$. The Petz map is $\Phi_B^*(Y)=B^{1/2}\Phi^*(\Phi(B)^{-1/2}Y\Phi(B)^{-1/2})B^{1/2}$.
--
--   If $\mathcal A$ admits two nonzero orthogonal projections, then no admissible generator represents Chernoff distance on its whole density-operator space, and, for each fixed $r>0$, none represents $H_r$:
--
--   $$
--   exists f:\ C(\rho\Vert\sigma)=S_f(\rho\Vert\sigma)\ \forall\rho,\sigma;\qquad
--   exists f:\ H_r(\rho\Vert\sigma)=S_f(\rho\Vert\sigma)\ \forall\rho,\sigma.$$
--
--   The positive-rate scope is the operational parameter used in the proof; $r=0$ is excluded. Representation multiplicities do not change the algebraic nontriviality condition.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 30, Proposition 6.4

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

/-- Proposition 6.4, PDF p.30: nonrepresentability on a nontrivial algebra;
Hoeffding's operational rate is strictly positive, as used by the source proof. -/
theorem proposition_6_4 [Nonempty I] (A : Alg I) (ha : TwoProjections A) :
    (¬ ∃ f, RepresentsStateDivergence A chernoff f) ∧
    ∀ r > (0 : ℝ), ¬ ∃ f, RepresentsStateDivergence A (fun X Y => hoeffding X Y r) f := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
