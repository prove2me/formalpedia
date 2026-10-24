-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_remark_4_8
-- name    : QAlgorithms.Papers.Independent.Support50.P12.remark_4_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:37:23.99631+00:00
-- url     : https://prove2.me/theorems/902b0849-40f0-4df6-9a3a-1dfc4eb7b52e
-- title:
--   Remark 4.8
-- statement:
--   Let $\mathcal A_1\subseteq B(H_1)$ and $\mathcal A_2\subseteq B(H_2)$ be concrete unital algebras on nonzero finite-dimensional complex Hilbert spaces, and let $\Phi:\mathcal A_1\to\mathcal A_2$ be complex linear. The adjoint is for $\langle X,Y\rangle_{\rm HS}=\operatorname{Tr}X^*Y$. A substochastic map has a Schwarz-contracting adjoint; stochastic additionally means trace preserving. Let $A,B\in\mathcal A_{1,+}$. Powers are zero on kernels and traces are not normalized.
--
--   For operator convex $f$, let $M_f$ contain the positive maps monotone for $S_f$ on all positive pairs. This class is convex and closed under compatible composition. A co-Schwarz bound is $\Phi(X)^*\Phi(X)\le c\Phi(XX^*)$, $c\ge0$; it is equivalent, with the same $c$, to a Schwarz bound after transposing the input algebra. Co-substochastic means that the adjoint satisfies the co-Schwarz bound with $c=1$. Under trace preservation of $B$ and the alternative $\operatorname{Tr}\Phi(A)=\operatorname{Tr}A$ or $\omega(f)\ge0$,
--
--   $$S_f(\Phi(A)\Vert\Phi(B))\le S_f(A\Vert B)$$
--
--   also holds for co-substochastic maps. Every convex combination of a stochastic and a co-stochastic map belongs to $M_f$. This uses the paper's specific decomposability, without replacing it by the entire CP plus co-CP cone.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 20, Remark 4.8

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

/-- Remark 4.8, PDF pp.20–21: convex/compositional closure, transpose reduction,
co-substochastic monotonicity, and the stated stochastic/co-stochastic decomposability. -/
theorem remark_4_8 [Nonempty I] [Nonempty J] [Nonempty K]
    (A : Alg I) (B : Alg J) (C : Alg K) (f : ℝ → ℝ)
    (hf : DivergenceGenerator f) (hconv : SemidefiniteOperatorConvex f) :
    (∀ (Phi Psi : MatrixMap I J), AlgebraExtension A B Phi → AlgebraExtension A B Psi →
      MonotoneMap A f Phi → MonotoneMap A f Psi → ∀ t ∈ Icc (0 : ℝ) 1,
        MonotoneMap A f (((1 - t : ℝ) : ℂ) • Phi + (t : ℂ) • Psi)) ∧
    (∀ (Phi : MatrixMap I J) (Psi : MatrixMap J K), AlgebraExtension A B Phi → AlgebraExtension B C Psi →
      MonotoneMap A f Phi → MonotoneMap B f Psi → MonotoneMap A f (Psi.comp Phi)) ∧
    (∀ Phi : MatrixMap I J, AlgebraExtension A B Phi → ∀ c : ℝ,
      CoBound A Phi c ↔ ∃ Psi : MatrixMap I J, (∀ X ∈ A, Phi X = Psi (Xᵀ)) ∧
        0 ≤ c ∧ (∀ X : Mat I, Xᵀ ∈ A → X.PosSemidef → (Psi X).PosSemidef) ∧
        ∀ X : Mat I, Xᵀ ∈ A → LE ((Psi X)ᴴ * Psi X) ((c : ℂ) • Psi (Xᴴ * X))) ∧
    (∀ (Phi : MatrixMap I J), CoSubstochastic A B Phi → ∀ X ∈ A, ∀ Y ∈ A,
      X.PosSemidef → Y.PosSemidef → tr (Phi Y) = tr Y →
      (tr (Phi X) = tr X ∨ 0 ≤ recessionSlope f) → div f (Phi X) (Phi Y) ≤ div f X Y) ∧
    (∀ (Phi Psi : MatrixMap I J), AlgebraStochastic A B Phi → CoStochastic A B Psi →
      ∀ t ∈ Icc (0 : ℝ) 1, MonotoneMap A f (((1 - t : ℝ) : ℂ) • Phi + (t : ℂ) • Psi)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
