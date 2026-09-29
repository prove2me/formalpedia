-- Prove2me | Theorems.Thm_StationaryAction_galileo_law_of_chords
-- name    : StationaryAction.galileo_law_of_chords
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:45:00.261979+00:00
-- url     : https://prove2.me/theorems/c6b1c056-460a-44f4-aa0b-5aaa35341298
-- title:
--   Galileo's law of chords
-- statement:
--   Galileo's law of chords, §2.3 of the source: the time of descent from rest along a chord of a vertical circle does not depend on the chord.
--
--   Let a vertical circle have diameter $D > 0$, and consider the chord from the top of the circle making angle $\varphi \in (-\pi/2, \pi/2)$ with the vertical. Its length is $D\cos\varphi$, and by Galileo's postulate a body sliding from rest along it has the constant acceleration $g\cos\varphi$, the component of gravity along the plane. If the body covers the chord in time $t > 0$, so that
--
--   $$\tfrac{1}{2}\,(g\cos\varphi)\,t^2 = D\cos\varphi ,$$
--
--   then
--
--   $$t = \sqrt{\frac{2D}{g}},$$
--
--   which is independent of $\varphi$: all chords from the top of the circle are descended in the same time. This is the statement the source records as Galileo's "law of chords", obtained there from equations (2.1)–(2.2) and the geometric relation $D/\sqrt{h} = \text{constant}$ on a circle, and it is the result from which Galileo argued that a broken path beats the straight one and that the circular arc is the fastest descent.
--
--   **Formalization Note** The chord is specified by its inclination $\varphi$ to the vertical rather than by its endpoints, and the hypothesis states the uniformly accelerated law of fall along it; the restriction $|\varphi| < \pi/2$ keeps the chord non-degenerate.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. §2.3, pp. 17–19, Eqs. (2.1)–(2.3) and Figure 2.4 (law of chords).

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, §2.3, Eqs. (2.1)–(2.2), Galileo's law of chords. -/
theorem galileo_law_of_chords
    (g D phi t : ℝ) (hg : 0 < g) (hD : 0 < D)
    (hphi : phi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (ht : 0 < t)
    (hfall : g * Real.cos phi * t ^ 2 / 2 = D * Real.cos phi) :
    t = Real.sqrt (2 * D / g) := by sorry

end StationaryAction
