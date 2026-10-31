-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_low_dimension_boundary_continuity
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.low_dimension_boundary_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:14:10.618597+00:00
-- url     : https://prove2.me/theorems/b9bb6cfa-09c1-406d-8d77-bef60fdb0577
-- title:
--   Unnumbered main result: continuity across the distillability boundary in 2 by 2 and 2 by 3
-- statement:
--   Let $E$ be a finite real-valued functional on finite bipartite asymptotic resource products. Assume only that an actual asymptotic LOCC conversion $R^{\otimes x}\to S^{\otimes y}$, with $x>0$ and $y\ge0$, implies $yE(S)\le xE(R)$. Supplies mean independent integer copy counts with floors; conversion permits every positive error and rate slack, all sufficiently large block lengths, and unconditional normalized output. The same functional is used across positive finite local dimensions. Neither additivity nor continuity is assumed.
--
--   Fix a $2\times b$ bipartite system with $b=2$ or $b=3$. Let $\mathcal D$ be the set of densities with $E_d>0$. For every $\rho$ in the frontier of $\mathcal D$ relative to the full density space,
--
--   $$E(\rho)=0,\qquad E\text{ is continuous at }\rho.$$
--
--   The frontier and continuity are taken in trace-distance topology. The conclusion is genuine boundary continuity, with no normalization of $E$ and no extension to all measures in larger $2\times b$ systems.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 3, Unnumbered main result: continuity across the distillability boundary in 2 by 2 and 2 by 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF pp.1,3: all asymptotic measures continuously vanish at the
distillability boundary in 2 by 2 and 2 by 3. No normalization (10). -/
theorem low_dimension_boundary_continuity
    (E : SupplyProduct → ℝ) (hE : IsAsymptoticMeasure E)
    (b : ℕ) (hb : b = 2 ∨ b = 3)
    (rho : DensitySpace 2 b)
    (hboundary : rho ∈ frontier {sigma : DensitySpace 2 b | 0 < loccDistillable sigma.val}) :
    resourceSingleValue E rho.val = 0 ∧
      ContinuousAt (fun sigma : DensitySpace 2 b => resourceSingleValue E sigma.val) rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
