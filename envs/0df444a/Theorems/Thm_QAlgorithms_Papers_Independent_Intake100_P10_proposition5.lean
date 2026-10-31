-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition5
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:53:43.57468+00:00
-- url     : https://prove2.me/theorems/23d88067-0815-4895-8828-6aa8347479ee
-- title:
--   BB84 has one bit of both steerabilities
-- statement:
--   Let $a,x\in\{0,1\}$ and let $B=\mathbb C^2$. Define the four BB84 assemblage blocks by
--
--   $$\hat\rho_B^{0,0}=\tfrac12|0\rangle\langle0|,\quad\hat\rho_B^{1,0}=\tfrac12|1\rangle\langle1|,\quad\hat\rho_B^{0,1}=\tfrac12|+\rangle\langle+|,\quad\hat\rho_B^{1,1}=\tfrac12|-\rangle\langle-|,$$
--
--   where $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$. For Definitions 1 and 3, with all admissible Eve systems and binary logarithms,
--
--   $$S(\hat\rho)=S^R(\hat\rho)=1.$$
--
--   This evaluates the two measures on the specific constructed four-block example, rather than on arbitrary measurements of an entangled state.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 4, Proposition 5, (29)–(30)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P10

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (PositiveTraceClass operatorTrace partialTraceFirst partialTraceSecond IsQuantumOperation)

open QAlgorithms.Papers.Independent.Renew46.P08 (qcmi)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

/-- Proposition 5, PDF pp.4--5, (29)--(30): the constructed BB84 example. -/
theorem proposition5 :
    intrinsicSteerability bb84Assemblage = 1 ∧ restrictedSteerability bb84Assemblage = 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
