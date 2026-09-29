-- Prove2me | Theorems.Thm_SenTachyon_minimumEnergyDensity_tendsto_zero
-- name    : SenTachyon.minimumEnergyDensity_tendsto_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:36:09.73848+00:00
-- url     : https://prove2.me/theorems/951d5891-a4e6-4885-959a-78732d8ffab6
-- title:
--   Vanishing energy density at the tachyon minimum (large-torus limit)
-- statement:
--   Fix a string coupling $g>0$. For radii $R_1,R_2$ of the torus $T^2$, let $M(R_1,R_2,g)$ be the mass at the classical minimum of the tachyon potential of the D2–anti-D2 system with one unit of magnetic flux on each brane, computed on the T-dual torus as the mass of two D2-branes with radii $1/R_1,1/R_2$ and coupling $g/(R_1R_2)$. Then the energy per unit area on the original torus tends to zero as both radii go to infinity:
--   $$\lim_{R_1,R_2\to\infty}\frac{M(R_1,R_2,g)}{4\pi^2R_1R_2}=0 .$$
--
--   Since the magnetic field vanishes in the same limit, this is the paper's conclusion that at the minimum of the tachyon potential the negative potential energy exactly cancels the brane plus anti-brane tension.
--
--   **Formalization Note** The limit $R_1,R_2\to\infty$ is the product filter `atTop ×ˢ atTop` on $\mathbb R\times\mathbb R$. The physical input that the BPS mass (9) persists as parameters vary is built into the definition of $M$.
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, p. 3, eq. (11) and the paragraph following it

import Mathlib
import Definitions.Def_SenTachyon_Defs

open scoped ContDiff
open Filter Topology

namespace SenTachyon
theorem minimumEnergyDensity_tendsto_zero (g : ℝ) (hg : 0 < g) :
    Tendsto (fun R : ℝ × ℝ => minimumEnergyDensity R.1 R.2 g) (atTop ×ˢ atTop) (𝓝 0) := by sorry
end SenTachyon
