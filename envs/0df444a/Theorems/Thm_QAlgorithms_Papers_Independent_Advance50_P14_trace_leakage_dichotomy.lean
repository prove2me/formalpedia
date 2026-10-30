-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_trace_leakage_dichotomy
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.trace_leakage_dichotomy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:18:45.64027+00:00
-- url     : https://prove2.me/theorems/54aa6867-a111-490d-a2ac-bf0a80642f55
-- title:
--   Section V, equation (20): alternative-model rate dichotomy
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. An operation is CPTP; its separability constraint applies only to the specified input and output partitions. Consider the alternative operation model with $\sup_{\sigma\in\mathcal S}\inf_{\pi\in\mathcal S}\|\Lambda_n(\sigma)-\pi\|_1\to0$. Let $E_C^{\rm tr}$ and $E_D^{\rm tr}$ denote its formation cost and distillation yield. Then
--
--   $$\rho\in\mathcal S\ \Longrightarrow\ E_C^{\rm tr}(\rho)=E_D^{\rm tr}(\rho)=0,\qquad \rho\notin\mathcal S\ \Longrightarrow\ E_D^{\rm tr}(\rho)=+\infty.$$
--
--   For each entangled input, every finite nonnegative rate is realized by integer Bell-pair counts whose ratio converges to that rate. No entangled formation-cost value is asserted. This dichotomy describes the alternative model’s amplification of any entanglement.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 15, Section V, equation (20): alternative-model rate dichotomy

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF pp.15–16, Eq.(20): free states have zero cost and yield; every
entangled state has infinite distillation yield under trace-norm leakage.
No formation-cost value for an entangled state is asserted. -/
theorem trace_leakage_dichotomy {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (hrho : IsDensityMatrix rho) :
    (IsMultipartiteSeparable A rho → asymptoticFormationCost .trace A rho = 0 ∧
      distillableEntanglement .trace A rho = 0) ∧
    (¬ IsMultipartiteSeparable A rho → distillableEntanglement .trace A rho = ⊤ ∧
      ∀ r : ℝ, 0 ≤ r → ∃ k : ℕ → ℕ, DistillationProtocol .trace A rho k ∧
        Tendsto (fun n => (k n : ℝ) / (n + 1 : ℝ)) atTop (nhds r)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
