-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_real_gelfand_representation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.real_gelfand_representation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:19:01.179445+00:00
-- url     : https://prove2.me/theorems/e5f91a15-f39a-4b8a-a62c-5a63fd67883a
-- title:
--   Proposition 7.4
-- statement:
--   Let $B$ be a unital complex C*-algebra and let $A\subseteq B$ be a norm-closed unital real star subalgebra. Suppose every two elements of $A$ commute and every element is self-adjoint. Then there are a compact Hausdorff space $Z$ and a real unital star algebra isomorphism
--
--   $$\Psi:C(Z;\mathbb R)\longrightarrow A,\qquad\|\Psi(f)-\Psi(g)\|=\|f-g\|_\infty.$$
--
--   No complex scalar closure of $A$ is assumed.
--
--   This is the real Gelfand representation used in the real bounded spectral theorem.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 33, Proposition 7.4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Proposition 7.4, PDF p.33: real closed commutative self-graphAdjoint subalgebras of a complex C*-algebra. -/
theorem real_gelfand_representation {B : Type u} [CStarAlgebra B]
    (A : StarSubalgebra ℝ B) (hclosed : IsClosed (A : Set B))
    (hcomm : ∀ a b : A, (a : B) * (b : B) = (b : B) * (a : B))
    (hself : ∀ a : A, star (a : B) = (a : B)) :
    ∃ (Z : Type u) (t : TopologicalSpace Z),
      letI := t
      ∃ (hc : CompactSpace Z) (ht : T2Space Z),
        letI := hc
        letI := ht
        ∃ e : C(Z, ℝ) ≃⋆ₐ[ℝ] A, Isometry e := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
