-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_qutrit_cost_counterexample
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.qutrit_cost_counterexample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:57:34.869398+00:00
-- url     : https://prove2.me/theorems/bd653cc5-74bc-4876-80e6-17c76c6599e2
-- title:
--   §III unnumbered: three-qutrit counterexample to cost monogamy
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   On three qutrits set $|\psi\rangle=(|123\rangle-|132\rangle+|231\rangle-|213\rangle+|312\rangle-|321\rangle)/\sqrt6$ and $\rho=|\psi\rangle\langle\psi|$. The vector has norm one, $\rho_A=I_3/3$, and each of the $AB$ and $AC$ marginal costs is one ebit.
--
--   $$
--   E_C(\rho_{A:BC})=S(\rho_A)=\log_2 3<2=E_C(\rho_{AB})+E_C(\rho_{AC}).
--   $$
--
--   This is a fixed-state counterexample to entanglement-cost monogamy. The one-ebit marginal fact is credited in the source to Yura [17].
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 4, §III unnumbered: three-qutrit counterexample to cost monogamy

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.4, §III: the fixed signed three-qutrit counterexample, including its normalization, maximally mixed A marginal, log2(3) joint cost and one-ebit pair costs (credited there to Yura [17]). -/
theorem qutrit_cost_counterexample
     :
    let rho := pureDensity threeQutritAlternatingVector
    ‖threeQutritAlternatingVector‖ = 1 ∧
      traceRight rho = (1 / 3 : ℂ) • (1 : Op (Fin 3)) ∧
      finiteSystemPreparationCost rho = vnEntropy (traceRight rho) ∧
      vnEntropy (traceRight rho) = Real.logb 2 3 ∧
      Real.logb 2 3 < (1 : ℝ) + 1 ∧
      finiteSystemPreparationCost (marginalRA rho) = 1 ∧ finiteSystemPreparationCost (marginalRB rho) = 1 ∧
      finiteSystemPreparationCost rho < finiteSystemPreparationCost (marginalRA rho) + finiteSystemPreparationCost (marginalRB rho) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35
