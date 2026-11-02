-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_time_zero_density
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.time_zero_density
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:28:36.015683+00:00
-- url     : https://prove2.me/theorems/e8924609-715c-496f-bfb3-6a83580b2f4a
-- title:
--   Density and orthogonal geometry of the time-zero subspace
-- statement:
--   Let $(E,E_+,\theta)$ be reflection positive, with canonical quotient $q$, null space $N$, and $E_0=\{v\in E_+:\theta v=v\}$. If a linear subspace $D\subseteq E_0$ has dense image in $\widehat E$, then $D$ is dense in $E_0$ and $q(E_0)=\widehat E$. Moreover,
--   $$N=E_+\cap E_0^\perp=E_+\cap\theta(E_+)^\perp,$$
--   and $N\oplus E_0\oplus\theta(N)$ is an orthogonal direct sum and a closed subspace of $E$.
--
--   No group or cyclicity hypothesis is imposed, and the final closed subspace is not asserted to be all of $E$.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 15, Lemma 3.16

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Lemma 3.16, PDF p. 15. No one-parameter group or cyclicity assumption.
The final orthogonal sum is asserted closed, without asserting it is all of E. -/
theorem time_zero_density [hHilbert : CompleteSpace E] (r : ReflectionData E) (D : Submodule ℂ E)
    (hD : D ≤ timeZero r) (hDense : Dense (quotientImage r D)) :
    D.topologicalClosure = timeZero r ∧
    quotientImage r (timeZero r) = Set.univ ∧
    osNull r = r.plus ⊓ (timeZero r).orthogonal ∧
    osNull r = r.plus ⊓ (r.plus.map r.theta.toLinearMap).orthogonal ∧
    Submodule.IsOrtho (osNull r) (timeZero r) ∧
    Submodule.IsOrtho (osNull r) ((osNull r).map r.theta.toLinearMap) ∧
    Submodule.IsOrtho (timeZero r) ((osNull r).map r.theta.toLinearMap) ∧
    IsClosed ((osNull r ⊔ timeZero r ⊔ (osNull r).map r.theta.toLinearMap :
      Submodule ℂ E) : Set E) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
