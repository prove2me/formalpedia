-- Prove2me | Theorems.Thm_ReflectedBSDE_Existence_proposition_2_3
-- name    : ReflectedBSDE.Existence.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:51.498594+00:00
-- url     : https://prove2.me/theorems/4258450b-fe85-40ae-98d7-98fbc40def65
-- title:
--   Proposition 2.3 — $Y_t$ is the value of an optimal stopping problem
-- statement:
--   Let $(\xi,f,S)$ satisfy (i)–(iv) and $S_T\le\xi$, with moreover $S\in\mathcal S^2$. Let $(Y,Z,K)$ be a solution of the reflected BSDE satisfying (v)–(viii) and (v′). Then for each $t\in[0,T]$,
--   $$Y_t=\operatorname*{ess\,sup}_{v\in\mathcal T_t}E\Big[\int_t^vf(s,Y_s,Z_s)\,ds+S_v\mathbf 1_{\{v<T\}}+\xi\,\mathbf 1_{\{v=T\}}\ \Big|\ \mathcal F_t\Big],$$
--   where $\mathcal T_t$ is the set of stopping times $v$ with $t\le v\le T$, and the essential supremum is taken relative to $\mathcal F_t$.
--
--   The solution of the reflected BSDE is the value process of an optimal stopping problem: stop at $v<T$ and receive the obstacle, or wait until $T$ and receive $\xi$, with running reward $f(s,Y_s,Z_s)$ in between.
--
--   **Formalization Note** Two hypotheses are added. The first is $S\in\mathcal S^2$: under (iv) alone only $S^+$ is square integrable, so $S_v$ need not be integrable, and Lean's conditional expectation of a non-integrable variable is $0$. The paper's Remark 3.2 shows that this is no loss of generality. The second is (v′), which follows from (v) by Corollary 3.3 and which the paper's proof uses ("From (v) and (v′)"). The essential supremum is the predicate `IsEssSupOver` relative to $\mathcal F_t$.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 705 (PDF p. 4), Proposition 2.3, (2)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution
import Definitions.Def_ReflectedBSDE_Existence_OptimalStopping

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

/-- Proposition 2.3 (p. 705): for a solution of (v)–(viii) (hence of (v′)), and with the obstacle
in `𝒮²` (Remark 3.2), for each `t ∈ [0, T]`,
`Y_t = ess sup_{v ∈ 𝒯_t} E[∫ₜᵛ f(s, Y_s, Z_s) ds + S_v 1_{v<T} + ξ 1_{v=T} | 𝓕_t]`. -/
theorem proposition_2_3 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S)
    (hS2 : IsS2 (augmentedFiltration P hB) P T S)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (hZ : SatisfiesV (augmentedFiltration P hB) P T Z)
    (hsol : SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K)
    (hYK : SatisfiesVPrime (augmentedFiltration P hB) P T Y K) :
    ∀ t ≤ T, IsEssSupOver P (augmentedFiltration P hB t)
      (fun v : stoppingTimesBetween (augmentedFiltration P hB) t T =>
        condExp (augmentedFiltration P hB t) P (stoppingReward T ξ f S Y Z t v))
      (Y t) := by sorry

end ReflectedBSDE.Existence
