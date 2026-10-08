-- Prove2me | Theorems.Thm_TalagrandConc_Subsequences_configuration_concentration
-- name    : TalagrandConc.Subsequences.configuration_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:09.961985+00:00
-- url     : https://prove2.me/theorems/0ac399e2-5e8b-4e95-90bf-f7f3a28db94a
-- title:
--   Theorem 7.1.3 — configuration functions satisfy (7.1.3) and (7.1.4)
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $P = \mu^{\otimes N}$ the product probability on $\Omega^N$. Let $L_N : \Omega^N \to \mathbb N$ be a configuration function: for every $x \in \Omega^N$ there is $J \subseteq \{1,\dots,N\}$ with $\operatorname{card} J = L_N(x)$ such that $L_N(y) \ge \operatorname{card}\{i \in J;\ y_i = x_i\}$ for all $y \in \Omega^N$. Let $M$ be a median of $L_N$ under $P$. Then for all $u > 0$,
--   $$P(L_N \ge M + u) \le 2\exp\Big(-\frac{u^2}{4(M+u)}\Big), \qquad P(L_N \le M - u) \le 2\exp\Big(-\frac{u^2}{4M}\Big).$$
--
--   This is the abstract version of Theorem 7.1.2: every integer quantity certified by a configuration of exactly its own size concentrates on the scale $\sqrt M$ around its median.
--
--   **Formalization Note** $L_N$ is assumed measurable, which states the paper's convention (pp. 81–82) of treating all functions as measurable. When $M = 0$ Lean's division gives $u^2/(4M) = 0$, so the second bound reads $P(L_N \le -u) \le 2$; the event is empty in that case, so nothing is lost.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 154, Theorem 7.1.3 (with Eq. (7.1.7), and Eqs. (7.1.3)–(7.1.4) of p. 153)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic
import Definitions.Def_TalagrandConc_Subsequences_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.Subsequences

/-- Talagrand (1995), Theorem 7.1.3, p. 154. Let `(Ω, μ)` be a probability space,
`P = μ^{⊗N}` on `Ω^N`, and `L_N : Ω^N → ℕ` a configuration function (7.1.7) (measurable,
per the paper's convention of treating all functions as measurable). If `M` is a median of
`L_N`, then for all `u > 0`, (7.1.3) `P(L_N ≥ M + u) ≤ 2 exp(−u² / (4(M + u)))` and
(7.1.4) `P(L_N ≤ M − u) ≤ 2 exp(−u² / (4M))`. -/
theorem configuration_concentration {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (L : (Fin N → Ω) → ℕ)
    (hL : IsConfigurationFunction L) (hLm : Measurable L) (M : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian (Measure.pi fun _ : Fin N => μ) (fun x => (L x : ℝ)) M)
    (u : ℝ) (hu : 0 < u) :
    (Measure.pi fun _ : Fin N => μ) {x | M + u ≤ (L x : ℝ)} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (4 * (M + u))))) ∧
      (Measure.pi fun _ : Fin N => μ) {x | (L x : ℝ) ≤ M - u} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (4 * M)))) := by sorry

end TalagrandConc.Subsequences
