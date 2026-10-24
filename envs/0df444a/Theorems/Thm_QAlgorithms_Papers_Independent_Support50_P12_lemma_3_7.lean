-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_lemma_3_7
-- name    : QAlgorithms.Papers.Independent.Support50.P12.lemma_3_7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:25:49.249252+00:00
-- url     : https://prove2.me/theorems/5825e5f5-8eba-443b-a9eb-018b68f32050
-- title:
--   Lemma 3.7
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   Assume $\Phi$ is substochastic and some nonzero positive $B$ has $\operatorname{Tr}\Phi(B)=\operatorname{Tr}B$. Then
--
--   $$\|\Phi^*\|_S=\|\Phi^*\|=1.$$
--
--   The nonzero condition excludes the zero-map degeneracy.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 13, Lemma 3.7

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

/-- Lemma 3.7, PDF p.13: the nonzero trace-preserved input forces both adjoint norms to one. -/
theorem lemma_3_7 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (X : Mat I) (hX : X ∈ A) (hXp : X.PosSemidef)
    (hn : X ≠ 0) (ht : tr (Phi X) = tr X) :
    snorm B (channelAdjoint Phi) = 1 ∧ pnorm (channelAdjoint Phi) = 1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
