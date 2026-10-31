-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_separable_value_zero
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.separable_value_zero
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:07:20.547898+00:00
-- url     : https://prove2.me/theorems/96f194a3-d454-4b1b-a1d4-3d29b6afc9a9
-- title:
--   Proposition 2: vanishing on separable states
-- statement:
--   Let $E$ be a finite real-valued functional on finite bipartite asymptotic resource products. Assume only that an actual asymptotic LOCC conversion $R^{\otimes x}\to S^{\otimes y}$, with $x>0$ and $y\ge0$, implies $yE(S)\le xE(R)$. Supplies mean independent integer copy counts with floors; conversion permits every positive error and rate slack, all sufficiently large block lengths, and unconditional normalized output. The same functional is used across positive finite local dimensions. Neither additivity nor continuity is assumed.
--
--   For any normalized separable bipartite density $\rho$, where separability means a convex combination of local density products,
--
--   $$E(\rho)=0.$$
--
--   Both local spaces have positive finite dimension. No Bell-state normalization is required, and separability is not replaced by positivity of the partial transpose.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 2, Proposition 2: vanishing on separable states

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF p.2, Proposition 2: separable means the full convex hull of
local density products, not the PPT relaxation. No ebit normalization. -/
theorem separable_value_zero
    (E : SupplyProduct → ℝ) (hE : IsAsymptoticMeasure E)
    {a b : ℕ} [NeZero a] [NeZero b] (rho : VidalOperator a b)
    (hrho : IsDensityMatrix rho) (hsep : Entanglement.IsSeparableDensity rho) :
    resourceSingleValue E rho = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
