-- Prove2me | Theorems.Thm_StationaryAction_heron_law_of_reflection
-- name    : StationaryAction.heron_law_of_reflection
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:42:50.077794+00:00
-- url     : https://prove2.me/theorems/c2c03d3c-2348-4fd2-b166-26fa6bc2f558
-- title:
--   Heron's law of reflection from the shortest reflected path
-- statement:
--   The oldest minimisation argument in the source, §2.2: Heron of Alexandria's derivation of the law of reflection from the shortest path.
--
--   A ray leaves a point at height $a > 0$ above a plane mirror, touches the mirror at horizontal position $s$, and reaches a point at height $b > 0$ above the mirror, horizontally separated from the first by $d$. The total path length is
--
--   $$\Lambda(s) = \sqrt{a^2+s^2} + \sqrt{b^2+(d-s)^2}.$$
--
--   If the reflection point $x$ minimises $\Lambda$, then
--
--   $$\frac{x}{\sqrt{a^2+x^2}} = \frac{d-x}{\sqrt{b^2+(d-x)^2}},$$
--
--   i.e. the angle of incidence equals the angle of reflection, which is Heron's conclusion $\angle had = \angle eag$ reached by his reflected-point construction.
--
--   This is the historical starting point of the whole development: a law of physics obtained from a minimum principle rather than from a mechanical model, two millennia before Fermat, Maupertuis and Hamilton.
--
--   **Formalization Note** Minimality is global over all real reflection points, not merely local, which is the form Heron's argument actually establishes; the equal angles are expressed through their sines, as ratios read off the figure.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. §2.2, pp. 14–15, and Figure 2.1.

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, §2.2, Heron of Alexandria's law of reflection. -/
theorem heron_law_of_reflection
    (a b d x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmin : IsMinOn (fun s : ℝ => Real.sqrt (a ^ 2 + s ^ 2)
        + Real.sqrt (b ^ 2 + (d - s) ^ 2)) Set.univ x) :
    x / Real.sqrt (a ^ 2 + x ^ 2) = (d - x) / Real.sqrt (b ^ 2 + (d - x) ^ 2) := by sorry

end StationaryAction
