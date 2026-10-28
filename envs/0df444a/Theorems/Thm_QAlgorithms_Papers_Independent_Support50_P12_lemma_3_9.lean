-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_lemma_3_9
-- name    : QAlgorithms.Papers.Independent.Support50.P12.lemma_3_9
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:29:23.742581+00:00
-- url     : https://prove2.me/theorems/d2a70212-49a5-482b-a962-35e0be894a78
-- title:
--   Lemma 3.9
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   Assume $\Phi$ is Schwarz, put $c=\|\Phi\|_S$, and set $M_\Phi=\{X\in\mathcal A_1:\Phi(X)\Phi(X^*)=c\Phi(XX^*)\}$. Then
--
--   $$X\in M_\Phi\iff\Phi(X)\Phi(Z)=c\Phi(XZ)\quad\text{for every }Z\in\mathcal A_1.$$
--
--   The set $M_\Phi$ is a complex vector space closed under multiplication. This is a one-sided domain; no closure under adjoints is asserted.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 14, Lemma 3.9

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

/-- Lemma 3.9, PDF p.14: ONE-sided XX* multiplicative domain; no star closure is asserted. -/
theorem lemma_3_9 [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : AlgebraSchwarzMap A Phi) :
    let c := (snorm A Phi).toReal
    let D := {X : Mat I | X ∈ A ∧ Phi X * Phi (Xᴴ) = (c : ℂ) • Phi (X * Xᴴ)}
    (∀ X ∈ A, X ∈ D ↔ ∀ Z ∈ A, Phi X * Phi Z = (c : ℂ) • Phi (X * Z)) ∧
    (0 : Mat I) ∈ D ∧
    (∀ X ∈ D, ∀ Y ∈ D, X + Y ∈ D) ∧
    (∀ a : ℂ, ∀ X ∈ D, a • X ∈ D) ∧
    (∀ X ∈ D, ∀ Y ∈ D, X * Y ∈ D) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
