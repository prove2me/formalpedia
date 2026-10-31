-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition13
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition13
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:00:51.615694+00:00
-- url     : https://prove2.me/theorems/17678121-1e27-4458-b245-53776ff2cd21
-- title:
--   Restricted deterministic one-way LOCC monotonicity
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. Let $\{\mathcal K_z\}_z$ be an arbitrary Bob instrument, $q(x\mid x_f)$ an input channel independent of $z$, and $r(a_f\mid a,x,x_f,z)$ an output channel. Construct
--
--   $$\hat\sigma_{B'}^{a_f,x_f}=\sum_{a,x,z}q(x\mid x_f)r(a_f\mid a,x,x_f,z)\mathcal K_z(\hat\rho_B^{a,x}).$$
--
--   Then
--
--   $$S^R(\hat\sigma)\le S^R(\hat\rho).$$
--
--   This describes the deterministic restricted operation after summing out $z$. Bob’s output space may differ from his input space.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 12, Proposition 13, (139)–(141)

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

/-- Proposition 13, PDF pp.12--13, (139)--(159): input independent of z,
with z summed out as in (140); no branch-average strengthening. -/
theorem proposition13 : RestrictedDeterministicMonotonicity := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
