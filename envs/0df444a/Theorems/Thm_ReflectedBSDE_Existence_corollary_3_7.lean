-- Prove2me | Theorems.Thm_ReflectedBSDE_Existence_corollary_3_7
-- name    : ReflectedBSDE.Existence.corollary_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:33.760982+00:00
-- url     : https://prove2.me/theorems/b45945dd-922f-41e2-b427-3c881c89b381
-- title:
--   Corollary 3.7 — at most one solution with $Z\in\mathbb H^2$
-- statement:
--   Let $(\xi,f,S)$ satisfy (i)–(iv) and $S_T\le\xi$. If $(Y,Z,K)$ and $(Y',Z',K')$ are progressively measurable triples satisfying (v), (vi), (vii) and (viii), then they coincide: $Y$ and $Y'$, and $K$ and $K'$, are indistinguishable on $[0,T]$, and
--   $$E\int_0^T|Z_t-Z'_t|^2\,dt=0.$$
--
--   This is the uniqueness half of Theorem 5.2, stated under the weak integrability assumption (v) only.
--
--   **Formalization Note** Uniqueness of $Z$ holds only $dP\otimes dt$-almost everywhere, which is how it is stated. The hypotheses are (v) and (vi)–(viii), not (v′).
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 711 (PDF p. 10), Corollary 3.7

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

/-- Corollary 3.7 (p. 711): under (i)–(iv) there is at most one progressively measurable triple
satisfying (v), (vi), (vii) and (viii). -/
theorem corollary_3_7 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ)
    (hZ : SatisfiesV (augmentedFiltration P hB) P T Z)
    (hsol : SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K)
    (hZ' : SatisfiesV (augmentedFiltration P hB) P T Z')
    (hsol' : SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y' Z' K') :
    SameSolution P T Y Z K Y' Z' K' := by sorry

end ReflectedBSDE.Existence
