-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_theorem_4_3
-- name    : QAlgorithms.Papers.Independent.Support50.P12.theorem_4_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:33:59.650934+00:00
-- url     : https://prove2.me/theorems/71c9630f-9f63-4185-9c20-6cb701ae1e84
-- title:
--   Theorem 4.3
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   Assume $\Phi$ is substochastic, $\operatorname{Tr}\Phi(B)=\operatorname{Tr}B$, and $f$ is operator convex on the full positive semidefinite half-line. If $\operatorname{Tr}\Phi(A)=\operatorname{Tr}A$ or $\omega(f)\ge0$, then
--
--   $$S_f(\Phi(A)\Vert\Phi(B))\le S_f(A\Vert B).$$
--
--   The trace/slope alternative is essential outside the reference support. This is the paper's precise monotonicity theorem.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 17, Theorem 4.3

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

/-- Theorem 4.3, PDF pp.17–19: condition (4.10) is retained, including its disjunction. -/
theorem theorem_4_3 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A)
    (hXp : X.PosSemidef) (hYp : Y.PosSemidef) (htr : tr (Phi Y) = tr Y)
    (f : ℝ → ℝ) (hf : DivergenceGenerator f) (hconv : SemidefiniteOperatorConvex f)
    (halt : tr (Phi X) = tr X ∨ 0 ≤ recessionSlope f) :
    div f (Phi X) (Phi Y) ≤ div f X Y := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
