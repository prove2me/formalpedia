-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_eq_200_k_zero
-- name    : SpikedWishart.SoftEdge.eq_200_k_zero
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T09:05:29.258309+00:00
-- url     : https://prove2.me/theorems/30625e4d-39ec-4b7a-8c8a-9f4102817b03
-- title:
--   Case $k=0$ of (200): $\int_0^\infty\mathcal H_\infty\mathcal J_\infty = \int_0^\infty e^{-\varepsilon(u+y)}\mathrm{Ai}(u+y)\mathrm{Ai}(v+y)e^{\varepsilon(v+y)}$
-- statement:
--   For all real $\varepsilon$, vertices $c_H,c_J$ and $u,v$, with $\mathcal H_\infty,\mathcal J_\infty$ defined by (120), (122) for $k=0$,
--
--   $$\int_0^\infty\mathcal H_\infty(u+y)\,\mathcal J_\infty(v+y)\,dy=\int_0^\infty e^{-\varepsilon(u+y)}\mathrm{Ai}(u+y)\,\mathrm{Ai}(v+y)\,e^{\varepsilon(v+y)}\,dy .$$
--
--   Role: for $k=0$ the sum in (200) is empty, and this identity identifies the limit kernel with the conjugated Airy kernel, which gives the Tracy-Widom limit $F_0$ in the parent.
--
--   **Formalization Note**: for $k=0$ the integrands of (120), (122) are entire, so the identity holds for every vertex.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, Section 3.3, (200) with k = 0, and the Airy representation (10), (12), pp. 1647 and 1676

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open MeasureTheory

namespace SpikedWishart.SoftEdge

theorem eq_200_k_zero (ε cH cJ u v : ℝ) :
    (∫ y in Set.Ioi (0 : ℝ), Hinf ε 0 cH (u + y) * Jinf ε 0 cJ (v + y)) =
      ∫ y in Set.Ioi (0 : ℝ),
        ((Real.exp (-ε * (u + y)) * Ai (u + y) * Ai (v + y) * Real.exp (ε * (v + y)) : ℝ) : ℂ) := by sorry

end SpikedWishart.SoftEdge
