-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_reflection_geometry
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.reflection_geometry
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:31:06.788097+00:00
-- url     : https://prove2.me/theorems/e6b327c1-69c5-4aa1-894a-5869c09387c4
-- title:
--   Reflection-positive Hilbert space geometry
-- statement:
--   Let $E$ be a complex Hilbert space, $E_+$ a closed complex subspace, and $\theta$ a unitary involution whose reflected form is positive semidefinite on $E_+$. Let $\widehat E$ be the separated completion for this form, $q:E_+\to\widehat E$ its canonical map, $N=\ker q$ viewed in $E$, and $E_0=\{v\in E_+:\theta v=v\}$. The range of $q$ is dense, and for every $v\in E_+$,
--   $$\|qv\|^2=\langle\theta v,v\rangle,\qquad\|qv\|\leq\|v\|,\qquad \|qv\|=\|v\|\iff\theta v=v.$$
--   Moreover, $N$ is both the zero set of the reflected quadratic form and its radical; $N=E_+\cap\theta(E_+)^\perp$, and $E_0=E_+\cap\theta(E_+)$. Every linear subspace of $E_+$ on which $q$ preserves norm is contained in $E_0$.
--
--   These identities specify the null space and the maximal isometric part of OS quantization. Pairings in the Lean statement use Mathlib's conjugate-linear first argument.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 5, 1.1.geometry

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- The geometric identities following Definition 1.1, PDF p. 5.
The printed reversed signs on theta eigenvectors are corrected by the displayed
norm calculation: theta(vplus)=vplus and theta(vminus)=-vminus. -/
theorem reflection_geometry [hHilbert : CompleteSpace E] (r : ReflectionData E) :
    DenseRange (osQ r) ∧
    (∀ v : r.plus,
      ‖osQ r v‖ ^ 2 = (inner ℂ (r.theta (v : E)) (v : E)).re ∧
      ‖osQ r v‖ ≤ ‖(v : E)‖ ∧
      (‖osQ r v‖ = ‖(v : E)‖ ↔ r.theta (v : E) = (v : E))) ∧
    (∀ v : r.plus, ((v : E) ∈ osNull r ↔
      inner ℂ (r.theta (v : E)) (v : E) = 0) ∧
      ((v : E) ∈ osNull r ↔ ∀ w : r.plus,
        inner ℂ (r.theta (w : E)) (v : E) = 0)) ∧
    osNull r = r.plus ⊓ (r.plus.map r.theta.toLinearMap).orthogonal ∧
    timeZero r = r.plus ⊓ r.plus.map r.theta.toLinearMap ∧
    (∀ F : Submodule ℂ E, ∀ hF : F ≤ r.plus,
      (∀ v : F, ‖osQ r ⟨v, hF v.property⟩‖ = ‖(v : E)‖) →
      F ≤ timeZero r) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
