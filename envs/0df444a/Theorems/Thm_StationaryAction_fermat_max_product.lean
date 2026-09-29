-- Prove2me | Theorems.Thm_StationaryAction_fermat_max_product
-- name    : StationaryAction.fermat_max_product
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:45:39.63232+00:00
-- url     : https://prove2.me/theorems/5c0d18f2-fae7-4d0b-8849-8811ed7b8855
-- title:
--   Fermat's method of maxima and minima: the rectangle of largest area
-- statement:
--   The example with which the source introduces Fermat's method of maxima and minima, §2.4.1: divide a segment of length $b$ into two parts so that their product is largest.
--
--   For every real $b$, the function
--
--   $$a \;\longmapsto\; a\,(b - a)$$
--
--   attains its maximum at $a = b/2$, with maximal value $b^2/4$. In Fermat's own terms this is the isoperimetric problem for a rectangle of half-perimeter $b$, and equation (2.11) of the source, $a = b/2$: among all rectangles of a given perimeter, the square has the largest area.
--
--   Fermat obtained it by *adequating* the products $a(b-a)$ and $(a+e)(b-a-e)$, dividing by $e$ and then setting $e = 0$ — the procedure the source presents as the pre-history of the derivative, and the tool with which Fermat went on to derive the law of refraction.
--
--   **Formalization Note** The maximum is global over all real $a$, and no sign assumption is made on $b$; the inequality $a(b-a) \le b^2/4$ holds for every real $a$ and $b$.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. §2.4.1, pp. 23–24, Eqs. (2.9)–(2.11).

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, §2.4.1, Eqs. (2.9)–(2.11), Fermat's method of maxima and minima. -/
theorem fermat_max_product (b : ℝ) :
    IsMaxOn (fun a : ℝ => a * (b - a)) Set.univ (b / 2) := by sorry

end StationaryAction
