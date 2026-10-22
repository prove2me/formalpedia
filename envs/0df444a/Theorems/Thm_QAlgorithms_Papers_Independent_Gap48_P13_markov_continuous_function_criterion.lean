-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_markov_continuous_function_criterion
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.markov_continuous_function_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:47:26.641718+00:00
-- url     : https://prove2.me/theorems/12f71610-bad7-4af1-be36-5edee956e495
-- title:
--   Universal continuous-function criterion for quasifree Markovness
-- statement:
--   Let $A\ge0$ be a one-particle covariance on a finite-dimensional orthogonal sum $H_1\oplus H_2\oplus H_3$, and let $A_{ij}:H_j\to H_i$ denote its blocks. Markovness means the quasifree marginal entropy equality (36), with each entropy evaluated by $\operatorname{Tr}g$, where $g(x)=(x+1)\log(x+1)-x\log x$ and $0\log0=0$. Then
--
--   $$\omega_A\text{ is Markov}\quad\Longleftrightarrow\quad\forall f\in C(\mathbb R,\mathbb C),\ A_{12}f(A_{22})A_{23}=A_{13}.$$
--
--   In particular,
--
--   $$\omega_A\text{ is Markov}\ \Longrightarrow\ A_{13}=0.$$
--
--   Here $f(A_{22})$ is continuous spectral calculus. On a finite real spectrum, quantifying over all continuous functions on $\mathbb R$ has exactly the same strength as quantifying over continuous functions on that spectrum. The universal quantifier retains the spectral information of the source's closing characterization.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 21, Continuous-function-Markov-criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

/-- Closing continuous-function Markov criterion, PDF p.21: the universal
quantifier is inside the equivalence. The f=0 consequence is retained explicitly. -/
theorem markov_continuous_function_criterion (A : Mat (I ⊕ (J ⊕ K)))
    (hA : A.PosSemidef) :
    (IsMarkov A ↔ ∀ f : ℝ → ℂ, Continuous f →
      a12 A * realSpectrumFunction f (a22 A) * a23 A = a13 A) ∧
    (IsMarkov A → a13 A = 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
