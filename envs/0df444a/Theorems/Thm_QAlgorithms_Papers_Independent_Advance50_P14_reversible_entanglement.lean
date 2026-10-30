-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_reversible_entanglement
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.reversible_entanglement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:13:12.273718+00:00
-- url     : https://prove2.me/theorems/97670242-d6b3-4c7c-b0db-732f28310716
-- title:
--   Theorem I, equation (2): reversible multipartite entanglement
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. Bell pairs shared by the first two parties are the currency. Integer copy counts are nonnegative, blocklengths are positive, and both approximation error and the uniform global-robustness leakage tend to zero absolutely. Let $E_C^{\rm ane}$ and $E_D^{\rm ane}$ be the infimum of the limsup formation rates and supremum of the liminf distillation rates, respectively, over these protocols. For every state $\rho$, the positive-block entropy ratios converge, and
--
--   $$E_C^{\rm ane}(\rho)=E_D^{\rm ane}(\rho)=E_R^\infty(\rho),\qquad E_R^\infty(\rho)=\lim_{n\to\infty}\frac{E_R(\rho^{\otimes n})}{n}.$$
--
--   Here $E_R$ is the minimum support-aware quantum relative entropy from a separable state. The theorem includes separable inputs and describes reversible asymptotic entanglement manipulation.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 6, Theorem I, equation (2): reversible multipartite entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF pp.6–7, Theorem I, Eq.(2): reversible asymptotically non-entangling
cost and yield, including separable states. Existence of the printed limit is
part of the conclusion, rather than a hypothesis. -/
theorem reversible_entanglement {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (hrho : IsDensityMatrix rho) :
    asymptoticFormationCost .ane A rho = distillableEntanglement .ane A rho ∧
    distillableEntanglement .ane A rho = ENNReal.ofReal (regularizedMultipartiteEntanglement A rho) ∧
    Tendsto (fun n => multipartiteRelativeEntanglement (powerRegister A (n + 1))
      (powerDensity A rho (n + 1)) / (n + 1 : ℝ))
      atTop (nhds (regularizedMultipartiteEntanglement A rho)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
