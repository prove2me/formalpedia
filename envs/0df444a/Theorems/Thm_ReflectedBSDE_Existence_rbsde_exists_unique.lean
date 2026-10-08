-- Prove2me | Theorems.Thm_ReflectedBSDE_Existence_rbsde_exists_unique
-- name    : ReflectedBSDE.Existence.rbsde_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:17.555704+00:00
-- url     : https://prove2.me/theorems/8c996a58-f39b-44bd-9655-90232a7fd3c3
-- title:
--   Theorem 5.2 — the reflected BSDE has a unique solution
-- statement:
--   Let $B$ be a $d$-dimensional standard Brownian motion on $(\Omega,\mathcal F,P)$, and let $(\mathcal F_t)$ be its natural filtration augmented by the $P$-null sets. Let $T\ge0$, and let the data $(\xi,f,S)$ satisfy:
--
--   1. (i) $\xi$ is $\mathcal F_T$-measurable with $E\xi^2<\infty$;
--   2. (ii) $f(\cdot,y,z)$ is progressively measurable with $E\int_0^Tf(t,y,z)^2dt<\infty$ for every $(y,z)$;
--   3. (iii) $f$ is Lipschitz in $(y,z)$ with a constant $K>0$, uniformly in $(t,\omega)$;
--   4. (iv) $S$ is a continuous progressively measurable obstacle with $E\sup_{0\le t\le T}(S_t^+)^2<\infty$;
--   5. $S_T\le\xi$ almost surely.
--
--   Then the reflected backward SDE
--   $$Y_t=\xi+\int_t^Tf(s,Y_s,Z_s)\,ds+K_T-K_t-\int_t^T(Z_s,dB_s),\qquad Y_t\ge S_t,\qquad \int_0^T(Y_t-S_t)\,dK_t=0,$$
--   with $K$ continuous, nondecreasing and $K_0=0$, has a solution $(Y,Z,K)$ with $E\int_0^T|Z_t|^2dt<\infty$, which moreover satisfies $E\sup_{t\le T}Y_t^2<\infty$ and $EK_T^2<\infty$. Any two solutions with $E\int_0^T|Z_t|^2dt<\infty$ coincide: their $Y$'s and $K$'s are indistinguishable on $[0,T]$, and their $Z$'s agree $dP\otimes dt$-almost everywhere.
--
--   This is the main well-posedness result of the paper. It underlies the optimal stopping and control interpretations of the reflected BSDE and its link with the obstacle problem for parabolic PDEs.
--
--   **Formalization Note** "The RBSDE with (v), (vi), (vii), (viii)" is `SatisfiesV ∧ SolvesRBSDE` on the augmented filtration. The existence part also asserts (v′), which follows by Corollary 3.3. The uniqueness part assumes only (v). The equations hold almost surely for all $t\in[0,T]$ simultaneously, with a continuous version of the Itô integral.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 718 (PDF p. 17), Theorem 5.2

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

/-- Theorem 5.2 (p. 718): under (i)–(iv) and `S_T ≤ ξ`, the RBSDE with (v)–(viii) has a solution
`(Y, Z, K)` (which moreover satisfies (v′)), and any two solutions satisfying (v)–(viii) agree. -/
theorem rbsde_exists_unique {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S) :
    (∃ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ),
        SatisfiesV (augmentedFiltration P hB) P T Z ∧
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K ∧
        SatisfiesVPrime (augmentedFiltration P hB) P T Y K) ∧
    ∀ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
      (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
      SatisfiesV (augmentedFiltration P hB) P T Z →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K →
      SatisfiesV (augmentedFiltration P hB) P T Z' →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y' Z' K' →
      SameSolution P T Y Z K Y' Z' K' := by sorry

end ReflectedBSDE.Existence
