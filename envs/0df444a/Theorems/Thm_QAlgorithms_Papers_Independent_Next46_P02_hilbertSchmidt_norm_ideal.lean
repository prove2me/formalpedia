-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_hilbertSchmidt_norm_ideal
-- name    : QAlgorithms.Papers.Independent.Next46.P02.hilbertSchmidt_norm_ideal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:27:54.940643+00:00
-- url     : https://prove2.me/theorems/285893ab-88f3-49cc-abac-392a05711695
-- title:
--   All Hilbert–Schmidt norm and ideal properties
-- statement:
--   Let $H$ be a complete real or complex Hilbert space. Define $\mathcal B_2(H)$ by square summability of $\|Te_i\|$ in a complete orthonormal basis, and $\|T\|_2=(\sum_i\|Te_i\|^2)^{1/2}$. This class is a linear space and the displayed function is a norm, including definiteness, homogeneity and the triangle inequality. For every bounded $S$ and every $T\in\mathcal B_2(H)$, both products belong to the class and
--
--   $$
--   \max\{\|ST\|_2,\|TS\|_2\}\le\|S\|\,\|T\|_2.
--   $$
--
--   Thus the class is a two-sided ideal. Every member is compact and $\|T\|\le\|T\|_2$. For every bounded $T$, membership of $T$ and $T^*$ is equivalent, and on that class $\|T^*\|_2=\|T\|_2$.
--
--   These conclusions supply all five parts (a)–(e), including compactness rather than just an operator norm bound.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 10, §5, Lemma 5.1(a)–(e): Hilbert–Schmidt norm and ideal

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF pp.10–11, Lemma 5.1(a)–(e): full norm axioms, two-sided ideal closure
and estimate, compactness, domination, and adjoint invariance. -/
theorem hilbertSchmidt_norm_ideal :
    NormOn (F := F) (IsHilbertSchmidt (F := F) (H := H)) hilbertSchmidtNorm ∧
    (∀ (S T : H →L[F] H), IsHilbertSchmidt T →
      IsHilbertSchmidt (S.comp T) ∧ IsHilbertSchmidt (T.comp S) ∧
      max (hilbertSchmidtNorm (S.comp T)) (hilbertSchmidtNorm (T.comp S)) ≤
        ‖S‖ * hilbertSchmidtNorm T) ∧
    (∀ T : H →L[F] H, IsHilbertSchmidt T → IsCompactOperator T ∧ ‖T‖ ≤ hilbertSchmidtNorm T) ∧
    (∀ T : H →L[F] H, (IsHilbertSchmidt (ContinuousLinearMap.adjoint T) ↔ IsHilbertSchmidt T) ∧
      (IsHilbertSchmidt T → hilbertSchmidtNorm T = hilbertSchmidtNorm (ContinuousLinearMap.adjoint T))) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
