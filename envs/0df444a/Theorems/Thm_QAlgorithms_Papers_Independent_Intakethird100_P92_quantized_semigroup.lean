-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_quantized_semigroup
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.quantized_semigroup
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:26:24.358202+00:00
-- url     : https://prove2.me/theorems/bca82555-8b7c-450b-82f5-94523fdb3386
-- title:
--   The induced hermitian contraction semigroup
-- statement:
--   Let $(E,E_+,\theta)$ be reflection positive and let $(U_t)_{t\in\mathbb R}$ be a strongly continuous unitary one-parameter group satisfying $U_tE_+\subseteq E_+$ for $t>0$ and $\theta U_t\theta=U_{-t}$. For each $t\geq0$, the canonical quotient extension $\widehat U_t$ exists and is a hermitian contraction. It satisfies
--   $$\widehat U_tq(v)=q(U_tv),\qquad \widehat U_0=1,\qquad \widehat U_{s+t}=\widehat U_s\widehat U_t,\qquad\|\widehat U_t\|\leq1.$$
--   For every $x\in\widehat E$, the map $t\mapsto\widehat U_tx$ is continuous on $[0,\infty)$.
--
--   This is the strongly continuous version specified by Definition 3.1; cyclicity is not required. The operators are defined by their continuous extensions from the canonical quotient, not supplied independently.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 10, Proposition 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Proposition 3.2, PDF p. 10: quotient descent produces a strongly continuous
semigroup of hermitian contractions, including the identity at time zero. -/
theorem quantized_semigroup [hHilbert : CompleteSpace E] (r : ReflectionData E) (U : ReflectionGroup r) :
    (∀ t v, quantized r U t (osQ r v) = osQ r (positiveRestriction r U t v)) ∧
    quantized r U 0 = ContinuousLinearMap.id ℂ (OS r) ∧
    (∀ s t, quantized r U (s + t) = (quantized r U s).comp (quantized r U t)) ∧
    (∀ t, ‖quantized r U t‖ ≤ 1 ∧
      ∀ x y, inner ℂ (quantized r U t x) y = inner ℂ x (quantized r U t y)) ∧
    (∀ x, Continuous (fun t : ℝ≥0 => quantized r U t x)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
