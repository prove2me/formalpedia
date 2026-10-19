-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_output_representation
-- name    : QAlgorithms.Papers.Independent.Information100.P62.output_representation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:33:34.163507+00:00
-- url     : https://prove2.me/theorems/4f047e37-372c-4e95-b23b-dff01359cd09
-- title:
--   Theorem 2.17: representation on the output
-- statement:
--   Let $A\subseteq L(H)$ be a nonzero star-subalgebra with intrinsic unit projection $P$, and let $\Phi:L(H)\to L(K)$ be a channel. Exact correctability is equivalent to existence of a faithful complex-linear star-representation $\pi:A\to L(K)$ such that
--   $$\Phi(X)=\Phi(P)\pi(X)=\pi(X)\Phi(P)\quad(X\in A).$$
--   When correctable, one can choose $\pi(P)$ to be the orthogonal projection onto $\operatorname{im}\Phi(P)$. This describes the channel's action on the whole correctable algebra.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 19, Theorem 2.17: representation on the output

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.19, 20, Theorem 2.17: representation on the output. -/
theorem output_representation [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Submodule ℂ (Matrix I I ℂ))
    (P : Matrix I I ℂ) (hA : IsCornerAlgebra A P) :
    (Correctable F A P ↔ ∃ f : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ,
      RepresentationOn A f ∧ ∀ X ∈ A, F X = F P * f X ∧ F X = f X * F P) ∧
    (Correctable F A P → ∃ f : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ,
      RepresentationOn A f ∧ (∀ X ∈ A, F X = F P * f X ∧ F X = f X * F P) ∧ f P = support (F P)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
