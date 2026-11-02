-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_stieltjes_temperedness
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.stieltjes_temperedness
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:29:48.153705+00:00
-- url     : https://prove2.me/theorems/dc4b4982-850d-4551-8e60-db50f30a05b0
-- title:
--   Temperedness of a rotation-invariant Stieltjes measure
-- statement:
--   Let $d\geq1$ and let $\rho$ be a positive Borel measure on $[0,\infty)$ satisfying $\int_0^\infty(1+y^2)^{-1}\,d\rho(y)<\infty$. Define $\Theta(x)=\int_0^\infty(y^2+\|x\|^2)^{-1}\,d\rho(y)$ and $\nu=\Theta\,dx$ on $\mathbb R^d$. Then
--   $$\nu\text{ is tempered}\quad\Longleftrightarrow\quad d>2\;\text{ or }\;\left[d=1,\ \int_{[0,1]}y^{-1}\,d\rho(y)<\infty\right]\;\text{ or }\;\left[d=2,\ \int_{[0,1]}\log(y^{-1})\,d\rho(y)<\infty\right].$$
--   If $\nu$ is tempered and $d=1$ or $d=2$, then $\rho(\{0\})=0$. The reciprocal and logarithm at zero are infinite. Temperedness means finiteness of some polynomially weighted nonnegative integral.
--
--   This separates tail control, provided by tameness, from the dimension-dependent singularity at zero. The zero measure is allowed.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 43, Proposition A.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Proposition A.3, PDF pp. 43--44. Tameness alone does not imply absence of
an atom at zero; that conclusion is conditional on temperedness in d=1 or d=2. -/
theorem stieltjes_temperedness (d : ℕ) (hd : 0 < d) (rho : Measure ℝ≥0)
    (hTame : IsTame rho) :
    (IsTemperedMeasure (stieltjesMeasure d rho) ↔
      2 < d ∨
      (d = 1 ∧ (∫⁻ y in Set.Icc (0 : ℝ≥0) 1, (y : ℝ≥0∞)⁻¹ ∂rho) < ⊤) ∨
      (d = 2 ∧ (∫⁻ y in Set.Icc (0 : ℝ≥0) 1, logReciprocal y ∂rho) < ⊤)) ∧
    (IsTemperedMeasure (stieltjesMeasure d rho) → (d = 1 ∨ d = 2) → rho {0} = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
