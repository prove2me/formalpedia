-- Prove2me | Theorems.Thm_ThirdLawThermo_entropy_integral_tendsto_atTop_of_heatCapacity_ge
-- name    : ThirdLawThermo.entropy_integral_tendsto_atTop_of_heatCapacity_ge
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:55.607913+00:00
-- url     : https://prove2.me/theorems/7a043dfc-25fa-45a2-8138-c1560e60a0f7
-- title:
--   A heat capacity bounded below by a positive constant makes the entropy diverge
-- statement:
--   Let $C(T)$ be the heat capacity of a sample, let $T>0$, and suppose that $C$ is bounded below by a positive constant at low temperature: $C(t)\ge c>0$ for all $t\in(0,T]$. Assume that $C(t)/t$ is integrable on $[T_0,T]$ for each $T_0\in(0,T)$, so that the entropy difference
--   $$S(T)-S(T_0)=\int_{T_0}^{T}\frac{C(t)}{t}\,dt$$
--   is defined.
--
--   **Theorem.** The entropy difference diverges as $T_0\to0$:
--   $$\int_{T_0}^{T}\frac{C(t)}{t}\,dt\longrightarrow+\infty\qquad(T_0\to0^+).$$
--
--   Consequently a heat capacity bounded below by a positive constant near absolute zero violates the third law, with or without a power-law assumption.
-- source:
--   Wikipedia, "Third law of thermodynamics", revision oldid=1369622029, https://en.wikipedia.org/w/index.php?title=Third_law_of_thermodynamics&oldid=1369622029; section "Consequences", subsection "Specific heat", sentence after Eq. (12): "The same argument shows that it cannot be bounded below by a positive constant, even if we drop the power-law assumption."

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology

namespace ThirdLawThermo

theorem entropy_integral_tendsto_atTop_of_heatCapacity_ge (C : ℝ → ℝ) (c T : ℝ)
    (hc : 0 < c) (hT : 0 < T) (hC : ∀ t ∈ Set.Ioc 0 T, c ≤ C t)
    (hint : ∀ T₀ ∈ Set.Ioo 0 T,
      IntervalIntegrable (fun t => C t / t) MeasureTheory.volume T₀ T) :
    Tendsto (fun T₀ => ∫ t in T₀..T, C t / t) (𝓝[>] 0) atTop := by sorry

end ThirdLawThermo
