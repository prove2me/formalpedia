-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P09_sepp_distillation
-- name    : QAlgorithms.Papers.Independent.Advance50.P09.sepp_distillation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:31:17.244988+00:00
-- url     : https://prove2.me/theorems/928f966d-33b3-4891-9fbf-0ce000f01214
-- title:
--   One-shot SEPP distillation
-- statement:
--   Let $\rho$ be a normalized density operator on a finite multipartite Hilbert space $H=\bigotimes_{i=1}^{m+2}H_i$, where every local space has positive dimension. Separability means full multipartite separability. All logarithms are base two. Let $F(\alpha,\beta)=(\operatorname{Tr}\sqrt{\sqrt\alpha\,\beta\sqrt\alpha})^2$ be squared Uhlmann fidelity.
--
--   SEPP consists of actual completely positive trace-preserving maps that send every fully separable state to a fully separable state. The resource $\Psi_M$ is a rank-$M$ maximally entangled state shared by the first two parties, with one-dimensional resource registers at the remaining parties; every positive integer $M$ is allowed.
--
--   Here $E_{\min}^{\varepsilon}(\rho)=\max_{0\le A\le I,\,\operatorname{Tr}(A\rho)\ge1-\varepsilon}\min_{\sigma\in\mathcal S(H)}[-\log_2\operatorname{Tr}(A\sigma)]$ is the operator-smoothed min-relative entropy of entanglement, with $-\log_2 0=+\infty$.
--
--   For $0\le\varepsilon<1$, let $E_{D,\mathrm{SEPP}}^{(1),\varepsilon}(\rho)$ be the maximum of $\log_2 M$ over SEPP channels $\Lambda$ satisfying $F(\Lambda(\rho),\Psi_M)\ge1-\varepsilon$. This maximum exists, the smoothed min quantity is finite, and
--
--   $$
--   \left\lfloor E_{\min}^{\varepsilon}(\rho)\right\rfloor
--   \le E_{D,\mathrm{SEPP}}^{(1),\varepsilon}(\rho)
--   \le E_{\min}^{\varepsilon}(\rho).
--   $$
--
--   This bounds the operational one-shot distillation optimum by a test-operator entanglement measure.
--
--   **Formalization Note** The printed domain $\varepsilon\ge0$ is restricted to $\varepsilon<1$: otherwise arbitrary resource ranks satisfy the fidelity requirement and the stated maximum does not exist. Lean asserts attainment explicitly using a greatest attainable rate.
-- source:
--   One-shot rates for entanglement manipulation under non-entangling maps, arXiv:0905.2673v2, PDF p. 3, Theorem 1, Eq.(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P09

noncomputable section

open Filter Set

open scoped Topology Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P09

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

/-- PDF p.3, Theorem 1, Eq.(19). The printed eps >= 0 is corrected to
0 <= eps < 1: at eps >= 1, arbitrary ranks are feasible and the maximum does not exist.
The greatest attainable rate is used, rather than assuming that a supremum is attained. -/
theorem sepp_distillation {m : ℕ} (H : MultipartiteSystem m) (rho : MultipartiteOperator H)
    (hrho : IsDensityMatrix rho) (eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps < 1) :
    ∃ e d : ℝ, operatorSmoothMinEntanglement rho eps = (e : EReal) ∧
      IsGreatest (distillationRates rho eps) d ∧
      (⌊e⌋ : ℝ) ≤ d ∧ d ≤ e := by sorry

end QAlgorithms.Papers.Independent.Advance50.P09

end
