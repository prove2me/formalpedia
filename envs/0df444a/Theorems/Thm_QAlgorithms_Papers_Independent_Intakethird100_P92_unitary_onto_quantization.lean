-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_unitary_onto_quantization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.unitary_onto_quantization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:24:37.546498+00:00
-- url     : https://prove2.me/theorems/cd389673-b804-49a1-b0d6-df7b6d0d8454
-- title:
--   Quantization of unitaries preserving the positive subspace onto itself
-- statement:
--   Let $(E,E_+,\theta)$ be reflection positive, let $q:E_+\to\widehat E$ be its canonical quotient, and let $U$ be a unitary operator with $UE_+=E_+$. Then:
--   1. If $\theta U\theta=U$, the induced operator $\widehat U$ is unitary.
--   2. If $\theta U\theta=U^{-1}$, the induced operator satisfies $\widehat U^2=1$. There are closed orthogonal complementary subspaces $F,G\subseteq E$, invariant under $\theta,U,U^{-1}$, giving reflection-positive triples $(F,F\cap E_+,\theta|_F)$ and $(G,G\cap E_+,\theta|_G)$, such that $\widehat G=0$ and $(U|_F)^2=1$.
--   $$E=F\oplus G,\qquad q(G\cap E_+)=\{0\},\qquad U^2|_F=1.$$
--
--   The equation involving $q$ expresses $\widehat G=0$, because the reflected form on $G\cap E_+$ is the restricted ambient form. This statement keeps both alternatives and the existence of the invariant decomposition.
--
--   The positive subspace also splits as $E_+=(E_+\cap F)\oplus(E_+\cap G)$, so the decomposition is a direct sum of reflection-positive triples.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 9, Lemma 2.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Lemma 2.4, PDF p. 9. Both alternatives and the invariant decomposition
are retained. The Hilbert sum is orthogonal and Eplus splits into its
intersections with F and G. The zero OS space of G is expressed by vanishing of the canonical
quotient on G intersect Eplus. No erroneous formula for G from the proof is used. -/
theorem unitary_onto_quantization [hHilbert : CompleteSpace E] (r : ReflectionData E) (U : E ≃ₗᵢ[ℂ] E)
    (hOnto : r.plus.map U.toLinearMap = r.plus) :
    ((∀ x, r.theta (U (r.theta x)) = U x) →
      ∃ V : OS r ≃ₗᵢ[ℂ] OS r, ∀ v : r.plus,
        ∃ hv : U (v : E) ∈ r.plus, V (osQ r v) = osQ r ⟨U v, hv⟩) ∧
    ((∀ x, r.theta (U (r.theta x)) = U.symm x) →
      ∃ A : OS r →L[ℂ] OS r,
        (∀ v : r.plus, ∃ hv : U (v : E) ∈ r.plus,
          A (osQ r v) = osQ r ⟨U v, hv⟩) ∧
        A.comp A = ContinuousLinearMap.id ℂ (OS r) ∧
        ∃ F G : Submodule ℂ E,
          IsClosed (F : Set E) ∧ IsClosed (G : Set E) ∧
          Disjoint F G ∧ F ⊔ G = ⊤ ∧
          Submodule.IsOrtho F G ∧
          r.plus = (r.plus ⊓ F) ⊔ (r.plus ⊓ G) ∧
          F.map r.theta.toLinearMap = F ∧ G.map r.theta.toLinearMap = G ∧
          F.map U.toLinearMap = F ∧ G.map U.toLinearMap = G ∧
          F.map U.symm.toLinearMap = F ∧ G.map U.symm.toLinearMap = G ∧
          (∀ v : r.plus, (v : E) ∈ G → osQ r v = 0) ∧
          (∀ v ∈ F, U (U v) = v)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
