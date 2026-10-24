-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_7_4
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_7_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:49:54.905356+00:00
-- url     : https://prove2.me/theorems/bc5e4dea-a5fa-4b1c-8f21-dbc34a98539c
-- title:
--   Corollary 7.4
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   If the concrete observable algebra $\mathcal A$ is noncommutative, then
--
--   $$
--   exists f\text{ admissible}:\quad S_f(\rho\Vert\sigma)=\|\rho-\sigma\|_1\quad\text{for all density pairs in }\mathcal A.$$
--
--   The distance has no factor $1/2$. This is nonrepresentability on each noncommutative algebra, including representations with multiplicities.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 36, Corollary 7.4

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

/-- Corollary 7.4, PDF p.36: full trace-norm distance (no factor 1/2). -/
theorem corollary_7_4 [Nonempty I] (A : Alg I) (ha : Noncommutative A) :
    ¬ ∃ f, RepresentsStateDivergence A (fun rho sigma => (QAlgorithms.traceNorm (rho - sigma) : EReal)) f := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
