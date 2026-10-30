-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P09_sepp_formation
-- name    : QAlgorithms.Papers.Independent.Advance50.P09.sepp_formation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:31:59.968528+00:00
-- url     : https://prove2.me/theorems/e932d0b0-ab27-4f64-b6c7-7818a528b69c
-- title:
--   One-shot SEPP formation
-- statement:
--   Let $\rho$ be a normalized density operator on a finite multipartite Hilbert space $H=\bigotimes_{i=1}^{m+2}H_i$, where every local space has positive dimension. Separability means full multipartite separability. All logarithms are base two. Let $F(\alpha,\beta)=(\operatorname{Tr}\sqrt{\sqrt\alpha\,\beta\sqrt\alpha})^2$ be squared Uhlmann fidelity.
--
--   SEPP consists of actual completely positive trace-preserving maps that send every fully separable state to a fully separable state. The resource $\Psi_M$ is a rank-$M$ maximally entangled state shared by the first two parties, with one-dimensional resource registers at the remaining parties; every positive integer $M$ is allowed.
--
--   Define standard robustness $R(\alpha)$ as the smallest $s\ge0$ for which $(\alpha+s\omega)/(1+s)$ is separable for a separable normalized noise state $\omega$. Put $LR(\alpha)=\log_2(1+R(\alpha))$ and $LR^\varepsilon(\rho)=\min_{F(\beta,\rho)\ge1-\varepsilon}LR(\beta)$, where $\beta$ ranges over normalized states. For every $\varepsilon\ge0$, let $E_{C,\mathrm{SEPP}}^{(1),\varepsilon}(\rho)$ be the minimum of $\log_2M$ over SEPP channels satisfying $F(\rho,\Lambda(\Psi_M))\ge1-\varepsilon$. The minimum exists and
--
--   $$
--   LR^\varepsilon(\rho)\le E_{C,\mathrm{SEPP}}^{(1),\varepsilon}(\rho)
--   \le LR^\varepsilon(\rho)+1.
--   $$
--
--   This characterizes one-shot SEPP formation up to an additive bit using standard logarithmic robustness. At $\varepsilon\ge1$ both optimized quantities are zero.
-- source:
--   One-shot rates for entanglement manipulation under non-entangling maps, arXiv:0905.2673v2, PDF p. 3, Theorem 2, Eq.(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P09

noncomputable section

open Filter Set

open scoped Topology Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P09

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

/-- PDF p.3, Theorem 2, Eq.(20): standard robustness, with the full eps >= 0 domain. -/
theorem sepp_formation {m : ℕ} (H : MultipartiteSystem m) (rho : MultipartiteOperator H)
    (hrho : IsDensityMatrix rho) (eps : ℝ) (heps : 0 ≤ eps) :
    ∃ l c : ℝ, smoothLogRobustness rho eps = (l : EReal) ∧
      IsLeast (formationRates rho eps) c ∧ l ≤ c ∧ c ≤ l + 1 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P09

end
