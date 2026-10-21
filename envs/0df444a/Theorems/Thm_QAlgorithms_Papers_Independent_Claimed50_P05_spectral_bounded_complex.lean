-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_spectral_bounded_complex
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.spectral_bounded_complex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:17:49.372186+00:00
-- url     : https://prove2.me/theorems/a59dab67-c0d8-4de8-adb7-46484c7e2a7a
-- title:
--   Theorem 7.1 (Spectral Theorem: Bounded Operators, K = C)
-- statement:
--   Let $H$ be a complex Hilbert space and $A_1,\ldots,A_d\in L(H)$ be normal and pairwise commuting. Then
--
--   $$\exists!\ \Phi:M(\mathbb C^d)\to C(H)\text{ a Borel calculus with }\Phi(z_j)=A_j\quad(1\le j\le d).$$
--
--   The $z_j$ are coordinate functions. Normality includes the usual adjoint-product equality; no stronger input commutation is assumed.
--
--   This is the bounded complex joint spectral theorem.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 30, Theorem 7.1 (Spectral Theorem: Bounded Operators, K = C)

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

/-- Theorem 7.1, PDF pp.30–31: bounded commuting complex normal operators have a unique joint calculus. -/
theorem spectral_bounded_complex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {d : ℕ} (A : Fin d → E →L[ℂ] E) (hA : ∀ j, Normal (k := ℂ) (boundedGraph (A j)))
    (hcomm : ∀ i j, (A i).comp (A j) = (A j).comp (A i)) :
    ∃! F : Symbol (Fin d → ℂ) ℂ → Relation E, Calculus F ∧
      ∀ j, F (fullCoordinate j) = boundedGraph (A j) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
