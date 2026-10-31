-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_distillation_cost_sandwich
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.distillation_cost_sandwich
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:09:56.067989+00:00
-- url     : https://prove2.me/theorems/247fcc80-4767-4987-97c7-7efb7ce70f2d
-- title:
--   Proposition 5: distillable entanglement and cost sandwich (corrected inequality)
-- statement:
--   Let $E$ be a finite real-valued functional on finite bipartite asymptotic resource products. Assume only that an actual asymptotic LOCC conversion $R^{\otimes x}\to S^{\otimes y}$, with $x>0$ and $y\ge0$, implies $yE(S)\le xE(R)$. Supplies mean independent integer copy counts with floors; conversion permits every positive error and rate slack, all sufficiently large block lengths, and unconditional normalized output. The same functional is used across positive finite local dimensions. Neither additivity nor continuity is assumed.
--
--   Assume additionally $E(\Phi^+)=1$. For any density $\rho$ in positive finite bipartite local dimensions, let $E_d(\rho)$ be the supremal actual LOCC Bell-pair yield and $E_c(\rho)$ the infimal actual LOCC Bell-pair supply for preparing $\rho$. Then
--
--   $$E_d(\rho)\le E(\rho)\le E_c(\rho).$$
--
--   The printed Proposition 5 reverses both inequalities. The statement above follows the source's Eq.(6) and both explicit inequalities in its proof; its provenance is reference [9]. No optimizing finite-block protocol is assumed.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 2, Proposition 5: distillable entanglement and cost sandwich (corrected inequality)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF pp.1–2 (6), Proposition 5 [9]. Printed: Ed >= E >= Ec.
Changed: Ed <= E <= Ec. Why: both inequalities in the source's proof
and Eq.(6) have this direction. Bell normalization (10) is explicit. -/
theorem distillation_cost_sandwich
    (E : SupplyProduct → ℝ) (hE : IsAsymptoticMeasure E) (hunit : resourceSingleValue E phiPlusDensity = 1)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (rho : VidalOperator a b)
    (hrho : IsDensityMatrix rho) :
    loccDistillable rho ≤ resourceSingleValue E rho ∧ resourceSingleValue E rho ≤ loccEntanglementCost rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
