-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_markov_characterization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.markov_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:28:55.434815+00:00
-- url     : https://prove2.me/theorems/50cb142f-b4cd-4d7a-9ff6-870e285fdacd
-- title:
--   Surjective time-zero quantization, multiplicativity, and the Markov identity
-- statement:
--   Let $U$ be a reflection-positive strongly continuous unitary one-parameter group on $(E,E_+,\theta)$, with $E_0$ cyclic. Let $P:E\to E_0$ be the orthogonal projection, put $\varphi(t)=PU_tP^*$, and let $\Gamma=q|_{E_0}$. Let $P_+,P_0,P_-$ be the orthogonal projections onto $E_+,E_0,\theta(E_+)$. The following are equivalent: $\Gamma$ is onto (and hence unitary); $\varphi$ is multiplicative on $(0,\infty)$; and
--   $$P_+P_0P_-=P_+P_-.$$
--   If these conditions hold, then for every real $t$,
--   $$\varphi(t)=\Gamma^*\widehat U_{|t|}\Gamma.$$
--   In particular, $\Gamma$ intertwines the positive-time compression and the OS semigroup. Also $E=N\oplus E_0\oplus\theta(N)$ orthogonally, $E_+$ is maximal among $\theta$-positive linear subspaces, and $E_+$ is the closed linear span of $U_tE_0$, $t>0$.
--
--   All projections and $\Gamma$ are computed from the original data. The Markov identity and maximality are conclusions, not fields of an assumed realization.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 15, Proposition 3.17

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Proposition 3.17, PDF pp. 15--16: all three equivalent conditions and all
three consequences. The operator identity in (a) is expressed through every
matrix coefficient, so it does not require an assumed adjoint for Gamma. -/
theorem markov_characterization [hHilbert : CompleteSpace E] (r : ReflectionData E) (U : ReflectionGroup r)
    (hCyclic : IsCyclic U.group (timeZero r)) :
    (Function.Surjective (timeZeroQuotient r) ↔ CompressionMultiplicative r U) ∧
    (Function.Surjective (timeZeroQuotient r) ↔ MarkovCondition r) ∧
    (Function.Surjective (timeZeroQuotient r) →
      (∃ J : timeZero r ≃ₗᵢ[ℂ] OS r, ∀ v, J v = timeZeroQuotient r v) ∧
      (∀ t : ℝ, ∀ v w : timeZero r,
        inner ℂ (v : E) ((timeZeroCompression r U t w : timeZero r) : E) =
          inner ℂ (timeZeroQuotient r v) (quantized r U ⟨|t|, abs_nonneg t⟩ (timeZeroQuotient r w))) ∧
      (∀ t : ℝ≥0, ∀ v : timeZero r,
        timeZeroQuotient r (timeZeroCompression r U t v) = quantized r U t (timeZeroQuotient r v)) ∧
      (osNull r ⊔ timeZero r ⊔ (osNull r).map r.theta.toLinearMap = ⊤) ∧
      Submodule.IsOrtho (osNull r) (timeZero r) ∧
      Submodule.IsOrtho (osNull r) ((osNull r).map r.theta.toLinearMap) ∧
      Submodule.IsOrtho (timeZero r) ((osNull r).map r.theta.toLinearMap) ∧
      (∀ F : Submodule ℂ E, r.plus ≤ F →
        (∀ v : F, 0 ≤ (inner ℂ (r.theta (v : E)) (v : E)).re) → F = r.plus) ∧
      (orbitSpan U.group (timeZero r) (Set.Ioi 0)).topologicalClosure = r.plus) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
