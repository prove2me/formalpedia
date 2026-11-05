-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_Jinf_vertex_shift
-- name    : SpikedWishart.SoftEdge.Jinf_vertex_shift
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T06:29:16.933353+00:00
-- url     : https://prove2.me/theorems/0d49b16b-467d-414d-a194-81ede6c06bb5
-- title:
--   $\mathcal J_\infty$ does not depend on the vertex of its contour
-- statement:
--   For all real $\varepsilon,v$, $k\in\mathbb N$ and vertices $c,c'$, the limit function (122) with vertex $c$ equals the one with vertex $c'$:
--
--   $$\mathcal J_\infty^{(c)}(v)=\mathcal J_\infty^{(c')}(v).$$
--
--   Role: lets part (ii) place the vertex of $\Sigma_\infty$ where the rescaled finite-$M$ contour puts it.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, (122) and the choice of the vertex of $\Sigma_\infty$, proof of Proposition 3.1, pp. 1661-1664

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem Jinf_vertex_shift :
    ∀ (ε : ℝ) (k : ℕ) (c c' v : ℝ), Jinf ε k c v = Jinf ε k c' v := by sorry

end SpikedWishart.SoftEdge
