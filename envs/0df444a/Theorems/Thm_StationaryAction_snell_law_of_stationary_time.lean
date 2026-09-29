-- Prove2me | Theorems.Thm_StationaryAction_snell_law_of_stationary_time
-- name    : StationaryAction.snell_law_of_stationary_time
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:39:35.362357+00:00
-- url     : https://prove2.me/theorems/f6597ea6-6e6a-43e2-9216-904b8d19743c
-- title:
--   Snell's law from Fermat's principle of least time
-- statement:
--   Fermat's derivation of the law of refraction, §2.4 of the source, in the modern coordinates of the figure.
--
--   Light travels from a point at height $a > 0$ above a plane interface to a point at depth $b > 0$ below it, the two points being horizontally separated by $d$, with speeds $v_1 > 0$ above and $v_2 > 0$ below. If the ray crosses the interface at horizontal position $s$, the travel time is
--
--   $$T(s) = \frac{\sqrt{a^2 + s^2}}{v_1} + \frac{\sqrt{b^2 + (d-s)^2}}{v_2}.$$
--
--   If $x$ is a stationary point of $T$, then
--
--   $$\frac{1}{v_1}\,\frac{x}{\sqrt{a^2+x^2}} = \frac{1}{v_2}\,\frac{d-x}{\sqrt{b^2+(d-x)^2}},$$
--
--   which is exactly $\frac{\sin\theta_1}{v_1} = \frac{\sin\theta_2}{v_2}$, equation (2.19), the two fractions being the sines of the angles of incidence and refraction measured from the normal. As the source stresses, the velocities here appear in the denominators, the opposite of Descartes' form (2.8): Fermat's principle forces light to slow down in the denser medium.
--
--   **Formalization Note** The angles are not primitive objects: their sines are the ratios the figure defines them by, so the statement commits to no convention about angle ranges, and it holds for crossing points $x$ on either side of the foot of the perpendicular.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. §2.4, pp. 25–27, Eqs. (2.14)–(2.19).

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, §2.4, Eqs. (2.18)–(2.19), Fermat's least-time law of refraction. -/
theorem snell_law_of_stationary_time
    (a b d v₁ v₂ x : ℝ) (ha : 0 < a) (hb : 0 < b) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hstat : deriv (fun s : ℝ => Real.sqrt (a ^ 2 + s ^ 2) / v₁
        + Real.sqrt (b ^ 2 + (d - s) ^ 2) / v₂) x = 0) :
    x / Real.sqrt (a ^ 2 + x ^ 2) / v₁
      = (d - x) / Real.sqrt (b ^ 2 + (d - x) ^ 2) / v₂ := by sorry

end StationaryAction
