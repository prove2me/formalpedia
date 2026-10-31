-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_deterministic_LOCC_monotonicity
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.deterministic_LOCC_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:08:03.459597+00:00
-- url     : https://prove2.me/theorems/064127a0-07e9-4dca-94f4-f40323cb65fa
-- title:
--   Proposition 3: deterministic LOCC monotonicity
-- statement:
--   Let $E$ be a finite real-valued functional on finite bipartite asymptotic resource products. Assume only that an actual asymptotic LOCC conversion $R^{\otimes x}\to S^{\otimes y}$, with $x>0$ and $y\ge0$, implies $yE(S)\le xE(R)$. Supplies mean independent integer copy counts with floors; conversion permits every positive error and rate slack, all sufficiently large block lengths, and unconditional normalized output. The same functional is used across positive finite local dimensions. Neither additivity nor continuity is assumed.
--
--   Let $\rho$ be a density operator on positive finite bipartite local dimensions. Let $L$ be a deterministic adaptive LOCC transformation into another positive finite bipartite system. Then
--
--   $$E(L(\rho))\le E(\rho).$$
--
--   Local instruments have complete rectangular Kraus families and outcome-dependent continuations; all terminal outcomes are summed. This is unconditional deterministic monotonicity, with local ancillas and disposal permitted.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 2, Proposition 3: deterministic LOCC monotonicity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF p.2, Proposition 3: deterministic adaptive LOCC monotonicity.
The accepted tree sums every outcome and permits arbitrary local scratch dimensions. -/
theorem deterministic_LOCC_monotonicity
    (E : SupplyProduct → ℝ) (hE : IsAsymptoticMeasure E)
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (rho : VidalOperator a b) (hrho : IsDensityMatrix rho)
    (L : Superop (Fin a × Fin b) (Fin c × Fin d)) (hL : FiniteLOCC L) :
    resourceSingleValue E (L rho) ≤ resourceSingleValue E rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
