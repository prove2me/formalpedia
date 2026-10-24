-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_lemma_4_2
-- name    : QAlgorithms.Papers.Independent.Support50.P12.lemma_4_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:33:14.686252+00:00
-- url     : https://prove2.me/theorems/ec3e570e-e09e-425f-824c-da11d789a7f0
-- title:
--   Lemma 4.2
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   Assume $\Phi$ is substochastic and put $V(X)=\Phi^*(X\Phi(B)^{-1/2})B^{1/2}$. With Hilbert–Schmidt adjoints and order,
--
--   $$\|V\|\le1,\qquad V^*(L_AR_{B^{-1}})V\le L_{\Phi(A)}R_{\Phi(B)^{-1}}.$$
--
--   The draft expresses the operator inequality through every quadratic form on $\mathcal A_2$. If $\Phi^*$ is a $C^*$-morphism, $V$ is isometric when $\Phi(B)$ is invertible, and the operator comparison is equality when $B$ is invertible. The two invertibility assumptions have different roles.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 16, Lemma 4.2

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

/-- Lemma 4.2, PDF pp.16–17: operator comparison is stated through every
Hilbert–Schmidt quadratic form; the two invertibility refinements are separate. -/
theorem lemma_4_2 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A)
    (hXp : X.PosSemidef) (hYp : Y.PosSemidef) :
    (∀ Z ∈ B, (hs (modularContraction Phi Y Z) (modularContraction Phi Y Z)).re ≤ (hs Z Z).re) ∧
    (∀ Z ∈ B, tr ((modularContraction Phi Y Z)ᴴ * X * modularContraction Phi Y Z * supportPower Y (-1)) ≤
      tr (Zᴴ * Phi X * Z * supportPower (Phi Y) (-1))) ∧
    ((∀ Z ∈ B, ∀ W ∈ B, channelAdjoint Phi (Z * W) = channelAdjoint Phi Z * channelAdjoint Phi W ∧
      channelAdjoint Phi (Zᴴ) = (channelAdjoint Phi Z)ᴴ) →
      (IsUnit (Phi Y) → ∀ Z ∈ B, (hs (modularContraction Phi Y Z) (modularContraction Phi Y Z)).re = (hs Z Z).re) ∧
      (IsUnit Y → ∀ Z ∈ B, tr ((modularContraction Phi Y Z)ᴴ * X * modularContraction Phi Y Z * supportPower Y (-1)) =
        tr (Zᴴ * Phi X * Z * supportPower (Phi Y) (-1)))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
