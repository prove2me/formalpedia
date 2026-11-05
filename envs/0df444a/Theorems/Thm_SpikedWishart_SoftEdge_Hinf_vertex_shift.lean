-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_Hinf_vertex_shift
-- name    : SpikedWishart.SoftEdge.Hinf_vertex_shift
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T07:52:42.260189+00:00
-- url     : https://prove2.me/theorems/ea46ca4a-9603-4b46-b893-2d72d9f07f27
-- title:
--   $\mathcal H_\infty$ does not depend on the vertex $c<0$ of its contour
-- statement:
--   For all real $\varepsilon,u$, $k\in\mathbb N$ and vertices $c,c'<0$, the limit function (120) built on the contour $\Gamma_\infty$ with vertex $c$ equals the one with vertex $c'$:
--
--   $$\mathcal H_\infty^{(c)}(u)=\mathcal H_\infty^{(c')}(u).$$
--
--   Role: lets the proof of part (i) place the vertex of $\Gamma_\infty$ at $-\varepsilon/2$, matching the rescaled finite-$M$ contour.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, (120) and the choice of the vertex of $\Gamma_\infty$ in $(-\varepsilon,0)$, proof of Proposition 3.1, pp. 1661-1664

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem Hinf_vertex_shift :
    ∀ (ε : ℝ) (k : ℕ) (u c c' : ℝ), c < 0 → c' < 0 → Hinf ε k c u = Hinf ε k c' u := by sorry

end SpikedWishart.SoftEdge
