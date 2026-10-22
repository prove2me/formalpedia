-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_operational_cost_upper_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.operational_cost_upper_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:29:41.033593+00:00
-- url     : https://prove2.me/theorems/6d461118-870a-47fd-b6ed-b75fbab09778
-- title:
--   Operational entanglement-cost upper bound
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Let $E_C(\rho)$ be the operational asymptotic number of shared singlets consumed per copy to form $\rho$ by unconditional two-way LOCC, with arbitrarily small output error. Then $$E_{\mathrm{sq}}(\rho)\le E_C(\rho).$$ The cost is a state-formation resource rate, as in the source, and supplies an operational upper bound.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 3, §II, Corollary 6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32

namespace QAlgorithms.Papers.Independent.Gap48.P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

local notation "sq" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "cmi" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "mi" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "ef" => QAlgorithms.Papers.Independent.Information100.P08.formation

-- Reuse exact accepted generic tensor pairing and partial traces.

open QAlgorithms.Papers.Independent.Next46.P42 (regroupProduct)

open QAlgorithms.Papers.Independent.Information100.P08 (firstPair secondPair)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

/-- PDF p.3, Corollary 6: comparison with operational STATE formation cost.
The accepted cost is defined via LOCC singlet consumption and paperBures error. -/
theorem operational_cost_upper_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho) :
    sq rho ≤ QAlgorithms.Papers.Independent.Dependency50.P42.entanglementCost
      QAlgorithms.Papers.Independent.Dependency50.P42.paperBures rho := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P32
