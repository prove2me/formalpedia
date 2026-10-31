-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_tensor_power_extensivity
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.tensor_power_extensivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:06:21.640872+00:00
-- url     : https://prove2.me/theorems/254d4e9f-4054-4d3e-a4a6-189f97a8dbbe
-- title:
--   Proposition 1: tensor-power extensivity
-- statement:
--   Let $E$ be a finite real-valued functional on finite bipartite asymptotic resource products. Assume only that an actual asymptotic LOCC conversion $R^{\otimes x}\to S^{\otimes y}$, with $x>0$ and $y\ge0$, implies $yE(S)\le xE(R)$. Supplies mean independent integer copy counts with floors; conversion permits every positive error and rate slack, all sufficiently large block lengths, and unconditional normalized output. The same functional is used across positive finite local dimensions. Neither additivity nor continuity is assumed.
--
--   For a density operator $\rho$ on positive finite bipartite local dimensions and any integer $N\ge0$,
--
--   $$E(\rho^{\otimes N})=N E(\rho).$$
--
--   At $N=0$ the tensor product is the one-dimensional scalar density. This is extensivity for identical copies, without an assertion of additivity on independent different states.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 2, Proposition 1: tensor-power extensivity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF p.2, Proposition 1: identical-copy extensivity, including the
zero-copy scalar resource; no full tensor-product additivity is asserted. -/
theorem tensor_power_extensivity
    (E : SupplyProduct → ℝ) (hE : IsAsymptoticMeasure E)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (rho : VidalOperator a b)
    (hrho : IsDensityMatrix rho) (N : ℕ) :
    resourceSingleValue E (ownedCopies rho N) = (N : ℝ) * resourceSingleValue E rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
