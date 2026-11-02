-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_exponential_kernel_criterion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.exponential_kernel_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:30:30.949099+00:00
-- url     : https://prove2.me/theorems/855616a8-3832-4e8c-a49f-2ee619bd55f1
-- title:
--   Positive definiteness of an exponential hermitian kernel
-- statement:
--   Let $V$ be a vector space over $\mathbb K=\mathbb R$ or $\mathbb C$, and let $\beta:V\times V\to\mathbb K$ be a hermitian form, with the first argument linear; in the real case this means symmetric bilinear. Then
--   $$\bigl[(v,w)\mapsto e^{\beta(v,w)}\bigr]\text{ is positive definite}\quad\Longleftrightarrow\quad\beta(v,v)\geq0\text{ for every }v\in V.$$
--   Positive definiteness means that every finite Gram sum is a real nonnegative scalar. Degenerate forms and the zero vector space are included.
--
--   This criterion relates hermitian forms to exponential kernels. The scalar type `RCLike` uniformly covers both real and complex cases; positivity is not assumed to define the exponential.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 52, Lemma C.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Lemma C.5, PDF p. 52, simultaneously for real and complex vector spaces
(`RCLike`). The zero vector space and degenerate hermitian forms are included. -/
theorem exponential_kernel_criterion (K : Type*) [RCLike K]
    (V : Type v) [AddCommGroup V] [Module K V] (beta : V → V → K)
    (hBeta : IsHermitianForm K beta) :
    IsPositiveKernel K (fun x y => NormedSpace.exp (beta x y)) ↔
      ∀ x, ∃ a : ℝ, 0 ≤ a ∧ beta x x = (a : K) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
