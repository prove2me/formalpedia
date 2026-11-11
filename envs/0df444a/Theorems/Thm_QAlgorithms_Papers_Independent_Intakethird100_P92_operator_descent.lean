-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_operator_descent
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.operator_descent
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T06:24:03.847133+00:00
-- url     : https://prove2.me/theorems/92040d16-e81f-4fa4-b0f8-f362b0133793
-- title:
--   OS descent and adjoint compatibility for densely defined operators
-- statement:
--   Let $(E,E_+,\theta)$ be a reflection-positive complex Hilbert space with canonical quotient $q:E_+\to\widehat E$. Let $D\subseteq E_+$ be a linear subspace with $q(D)$ dense in $\widehat E$. Suppose $T,U:D\to E_+$ are linear and satisfy
--   $$\langle\theta Tv,w\rangle=\langle\theta v,Uw\rangle\quad(v,w\in D).$$
--   Both maps preserve $N\cap D$, where $N=\ker q$, and induce linear operators $\widehat T,\widehat U$ on the common domain $q(D)$ with $\widehat T(qv)=q(Tv)$ and $\widehat U(qv)=q(Uv)$. They satisfy $\widehat U\subseteq\widehat T^*$, equivalently the adjoint pairing identity on this dense domain. If $T=U$, then $\widehat T$ is symmetric. If additionally $D=E_+$ and $T$ is bounded, its induced operator has a continuous extension to $\widehat E$ satisfying $\|\widehat T\|\leq\|T\|$.
--
--   This result supplies descent, symmetry, and the norm estimate; none of them is assumed as input.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 8, Lemma 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Lemma 2.2, PDF pp. 8--9, all four clauses. The adjoint inclusion is stated
by its defining pairing identity on the dense common domain q(D), so it does not
incorrectly treat unbounded adjoints as everywhere-defined bounded operators.
The printed Eplus domain in (i) is D, as explicitly used in equation (5). -/
theorem operator_descent [hHilbert : CompleteSpace E] (r : ReflectionData E) (D : Submodule ℂ r.plus)
    (hDense : Dense ((D.map (osQ r) : Submodule ℂ (OS r)) : Set (OS r)))
    (T U : D →ₗ[ℂ] r.plus)
    (hPair : ∀ v w : D,
      inner ℂ (r.theta (T v : E)) (w : E) =
        inner ℂ (r.theta (v : E)) (U w : E)) :
    (∀ v : D, osQ r v = 0 → osQ r (T v) = 0 ∧ osQ r (U v) = 0) ∧
    ∃ Tq Uq : D.map (osQ r) →ₗ[ℂ] OS r,
      (∀ v, Tq (domainQ r D v) = osQ r (T v)) ∧
      (∀ v, Uq (domainQ r D v) = osQ r (U v)) ∧
      (∀ v w : D.map (osQ r),
        inner ℂ (Tq v) (w : OS r) = inner ℂ (v : OS r) (Uq w)) ∧
      (T = U → ∀ v w : D.map (osQ r),
        inner ℂ (Tq v) (w : OS r) = inner ℂ (v : OS r) (Tq w)) ∧
      (∀ B : r.plus →L[ℂ] r.plus, (∀ v : D, B v = T v) → D = ⊤ → T = U →
        (∀ v : r.plus, osExtension r B.toLinearMap (osQ r v) = osQ r (B v)) ∧
        (∀ v : D.map (osQ r), osExtension r B.toLinearMap v = Tq v) ∧
        ‖osExtension r B.toLinearMap‖ ≤ ‖B‖) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
