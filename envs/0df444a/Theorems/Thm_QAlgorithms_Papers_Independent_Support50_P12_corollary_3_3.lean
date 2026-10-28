-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_3_3
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_3_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:22:25.969977+00:00
-- url     : https://prove2.me/theorems/066ca148-2ffc-4d2e-957b-4c70af6aeeff
-- title:
--   Corollary 3.3
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   Assume $\Phi$ is positive and trace non-increasing. Then
--
--   $$\Phi\text{ preserves trace on }(A+B)^0\mathcal A_1(A+B)^0\iff\operatorname{Tr}\Phi(A)=\operatorname{Tr}A\ \text{and}\ \operatorname{Tr}\Phi(B)=\operatorname{Tr}B.$$
--
--   This identifies the support corner determined by a trace-preserved pair.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 11, Corollary 3.3

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

/-- Corollary 3.3, PDF p.11: preservation on a sum's support corner. -/
theorem corollary_3_3 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : PositiveOnConcreteAlgebra A Phi) (ht : AlgebraTraceNonincreasing A Phi)
    (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A) (hXp : X.PosSemidef) (hYp : Y.PosSemidef) :
    CornerTP A Phi (supp (X + Y)) ↔ tr (Phi X) = tr X ∧ tr (Phi Y) = tr Y := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
