-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_log_robustness_leakage
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.log_robustness_leakage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:15:28.129959+00:00
-- url     : https://prove2.me/theorems/f3961e5d-4506-4cdd-8928-647c158b309d
-- title:
--   Lemma IV.1, equation (8): log robustness leakage bound
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. An operation is CPTP; its separability constraint applies only to the specified input and output partitions. For $\epsilon\ge0$, let $\Lambda$ generate global robustness at most $\epsilon$ on every separable input, and let $LR_G(\rho)=\log_2(1+R_G(\rho))$. For every density matrix $\rho$,
--
--   $$LR_G(\Lambda(\rho))\le\log_2(1+\epsilon)+LR_G(\rho).$$
--
--   The leakage penalty is additive and uniform over all input states.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 8, Lemma IV.1, equation (8): log robustness leakage bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.8, Lemma IV.1, Eq.(8): the bound is ADDITIVE log2(1+epsilon). -/
theorem log_robustness_leakage {m l : ℕ} (A : MultipartiteRegister m) (B : MultipartiteRegister l)
    (rho : PartyOperator A) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ) (L : Superop (RegisterBasis A.Local) (RegisterBasis B.Local))
    (hL : EpsilonNonEntangling A B epsilon L) :
    logRobustness false B (L rho) ≤ Real.logb 2 (1 + epsilon) +
      logRobustness false A rho := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
