-- Prove2me | Theorems.Thm_TitiusBode_resonance_two_three
-- name    : TitiusBode.resonance_two_three
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:09.368965+00:00
-- url     : https://prove2.me/theorems/78e1f633-b0d3-4e4f-8fec-c9f3ffe2c0b3
-- title:
--   Footnote 1 — $2{:}3$ resonance: distances differ by $-23.69\%$ and $+31.04\%$
-- statement:
--   Let $K > 0$ and let $T_1, T_2$ be orbital periods with $T_1 > 0$ and $T_1 / T_2 = 2/3$ (a $2{:}3$ orbital resonance). Suppose the semi-major axes are given by Kepler's third law, $a_i = K\,T_i^{2/3}$. Then, rounded to two decimals, the relative deviations are
--
--   $$
--   100\cdot\frac{a_1 - a_2}{a_2} \approx -23.69, \qquad 100\cdot\frac{a_2 - a_1}{a_1} \approx +31.04,
--   $$
--
--   in the precise sense that each differs from the printed value by less than $0.005$.
--
--   This is the last sentence of footnote 1 to the data table of the source: planets in a $2{:}3$ orbital resonance vary in distance by $(2/3)^{2/3}$, i.e. $-23.69\%$ and $+31.04\%$ relative to one another.
--
--   **Formalization Note** Kepler's law appears only as the form $a_i = K T_i^{2/3}$ of the two semi-major axes; $T_i^{2/3}$ is the real power.
-- source:
--   Wikipedia, "Titius–Bode law", revision oldid=1372822920, https://en.wikipedia.org/w/index.php?title=Titius%E2%80%93Bode_law&oldid=1372822920, section "Data", footnote 1 to the table (last two sentences)

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology

namespace TitiusBode
theorem resonance_two_three (K T₁ T₂ : ℝ) (hK : 0 < K) (hT₁ : 0 < T₁)
    (hres : T₁ / T₂ = 2 / 3) :
    |100 * deviation (K * T₁ ^ ((2 : ℝ) / 3)) (K * T₂ ^ ((2 : ℝ) / 3)) - (-23.69)| < 0.005 ∧
    |100 * deviation (K * T₂ ^ ((2 : ℝ) / 3)) (K * T₁ ^ ((2 : ℝ) / 3)) - 31.04| < 0.005 := by sorry
end TitiusBode
