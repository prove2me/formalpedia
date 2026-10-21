-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_spectral_bounded_real
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.spectral_bounded_real
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:18:39.334217+00:00
-- url     : https://prove2.me/theorems/f45c5e9c-9f7c-405b-b11c-f33108620172
-- title:
--   Theorem 7.3 (Spectral Theorem: Bounded Operators, K = R)
-- statement:
--   Let $H$ be a real Hilbert space and $A_1,\ldots,A_d\in L(H)$ be self-adjoint and pairwise commuting. Then
--
--   $$\exists!\ \Phi:M(\mathbb R^d)\to C(H)\text{ a Borel calculus with }\Phi(z_j)=A_j\quad(1\le j\le d).$$
--
--   Real normality alone is not substituted for self-adjointness.
--
--   This is the bounded real joint spectral theorem.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 32, Theorem 7.3 (Spectral Theorem: Bounded Operators, K = R)

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

/-- Theorem 7.3, PDF pp.32–33: bounded real self-graphAdjoint, not merely real normal, operators. -/
theorem spectral_bounded_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {d : ℕ} (A : Fin d → E →L[ℝ] E) (hA : ∀ j, SelfAdjoint (k := ℝ) (boundedGraph (A j)))
    (hcomm : ∀ i j, (A i).comp (A j) = (A j).comp (A i)) :
    ∃! F : Symbol (Fin d → ℝ) ℝ → Relation E, Calculus F ∧
      ∀ j, F (fullCoordinate j) = boundedGraph (A j) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
