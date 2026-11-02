-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_eventual_entry_density
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.eventual_entry_density
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:27:31.233302+00:00
-- url     : https://prove2.me/theorems/73ce6164-1794-4008-adbc-7402e9b79328
-- title:
--   An eventual-entry criterion for density after OS quantization
-- statement:
--   Let $U$ be a reflection-positive strongly continuous unitary one-parameter group on $(E,E_+,\theta)$, and let $q:E_+\to\widehat E$ be the canonical quotient. Let $D\subseteq E_+$ be a linear subspace invariant under $U_t$ for all $t>0$. If
--   $$\{v\in E_+:\text{there is }T>0\text{ with }U_Tv\in D\}$$
--   is dense in $E_+$, then $q(D)$ is dense in $\widehat E$.
--
--   This is a density criterion on the original positive subspace; no cyclicity or prior density of $q(D)$ is assumed.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 11, Lemma 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Lemma 3.6, PDF p. 11. Density of the eventual-entry set in Eplus implies
density of the canonical image q(D), without assuming that density. -/
theorem eventual_entry_density [hHilbert : CompleteSpace E] (r : ReflectionData E) (U : ReflectionGroup r)
    (D : Submodule ℂ E) (hD : D ≤ r.plus)
    (hInv : ∀ t : ℝ, 0 < t → ∀ v ∈ D, U.group.op t v ∈ D)
    (hDense : Dense {v : r.plus | ∃ T : ℝ, 0 < T ∧ U.group.op T v ∈ D}) :
    Dense (quotientImage r D) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
