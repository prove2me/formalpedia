-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_lemma_3_8
-- name    : QAlgorithms.Papers.Independent.Support50.P12.lemma_3_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:27:39.218806+00:00
-- url     : https://prove2.me/theorems/09add383-d5cd-4471-8662-e0857537f349
-- title:
--   Lemma 3.8
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   The class of Schwarz maps is closed under composition, Hilbert–Schmidt adjoints, and nonnegative linear combinations. With the extended Schwarz norm,
--
--   $$\|a\Phi\|_S=a\|\Phi\|_S\quad(a\ge0),\qquad\|\Phi_1+\Phi_2\|_S\le\|\Phi_1\|_S+\|\Phi_2\|_S.$$
--
--   Here $0\cdot\infty=0$. Composed maps have compatible concrete domain and range algebras. These properties hold beyond two-positive maps.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 13, Lemma 3.8

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

/-- Lemma 3.8, PDF pp.13–14: closure under composition, adjoints and nonnegative
linear combinations, with the extended homogeneous and triangle bounds. -/
theorem lemma_3_8 [Nonempty I] [Nonempty J] [Nonempty K]
    (A : Alg I) (B : Alg J) (C : Alg K) (Phi Phi1 Phi2 : MatrixMap I J) (Psi : MatrixMap J K)
    (hc : AlgebraExtension A B Phi) (hc1 : AlgebraExtension A B Phi1) (hc2 : AlgebraExtension A B Phi2)
    (hd : AlgebraExtension B C Psi) :
    (AlgebraSchwarzMap A Phi → AlgebraSchwarzMap B Psi → AlgebraSchwarzMap A (Psi.comp Phi)) ∧
    (AlgebraSchwarzMap A Phi → AlgebraSchwarzMap B (channelAdjoint Phi)) ∧
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → AlgebraSchwarzMap A Phi1 → AlgebraSchwarzMap A Phi2 →
      AlgebraSchwarzMap A ((a : ℂ) • Phi1 + (b : ℂ) • Phi2)) ∧
    (∀ a : ℝ, 0 ≤ a → snorm A ((a : ℂ) • Phi) = ENNReal.ofReal a * snorm A Phi) ∧
    snorm A (Phi1 + Phi2) ≤ snorm A Phi1 + snorm A Phi2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
