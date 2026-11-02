-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P36_operational_parametrization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P36.operational_parametrization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:20:40.335888+00:00
-- url     : https://prove2.me/theorems/388c3cf0-18de-4b27-ad72-98e742d84c7c
-- title:
--   Operational parametrization and success probability of 1W-LOCC
-- statement:
--   Let \(\rho_{a|x}\) be a positive, no-signaling finite-dimensional assemblage of common trace \(t\le1\). Bob first applies rectangular Kraus operators \(K_w\) with \(\sum_w K_w^\dagger K_w\le I\). He communicates \(w\) to Alice, who samples \(x\) from a normalized law \(P(x|x_f,w)\), obtains the original output \(a\), and samples \(a_f\) from a normalized law \(P(a_f|a,x,w,x_f)\). The resulting protocol has exactly the action
--
--   $$
--   (M\rho)_{a_f|x_f}=\sum_{w,a,x}P(x|x_f,w)P(a_f|a,x,w,x_f)K_w\rho_{a|x}K_w^\dagger.
--   $$
--
--   Its output is an assemblage. For each branch, the trace is \(p_w=\operatorname{Tr}(K_w\rho_BK_w^\dagger)\), independently of \(x_f\), where \(\rho_B=\sum_a\rho_{a|x}\). Consequently \(\operatorname{Tr}M(\rho)=\sum_wp_w\le t\); equality holds for a complete Kraus family. The data specify the sequential protocol as well as its closed formula, providing the operational meaning of the parametrization.
-- source:
--   The resource theory of steering, arXiv:1409.5804v3, PDF p. 3, Section III, (9)–(12); Appendix A

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P36

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

variable {d r s df rf sf m : ℕ}

/-- Section III and Appendix A, PDF pp.3–4,9–10, (9)–(12),(A6): the sequential
protocol has exactly the parametrized action and the stated success probability. -/
theorem operational_parametrization (P : SteeringProtocol d r s df rf sf m)
    (rho : AssemblageBlocks d r s) (hrho : IsAssemblage rho) :
    protocolAction P rho = oneWayFormula P rho ∧
    IsAssemblage (protocolAction P rho) ∧
    (∀ w xf, (∑ af, protocolBranch P rho w af xf).trace.re = steeringBranchProbability P rho w) ∧
    assemblageMass (protocolAction P rho) = ∑ w, steeringBranchProbability P rho w ∧
    assemblageMass (protocolAction P rho) ≤ assemblageMass rho ∧
    (P.Complete → assemblageMass (protocolAction P rho) = assemblageMass rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P36

end
