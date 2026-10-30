-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P09_smoothMax_deltaSEPP_monotone
-- name    : QAlgorithms.Papers.Independent.Advance50.P09.smoothMax_deltaSEPP_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:34:13.601521+00:00
-- url     : https://prove2.me/theorems/0d374109-3699-4e43-8bff-e0f8caf72ca7
-- title:
--   Smooth max entanglement under delta-SEPP maps
-- statement:
--   Let $\rho$ be a normalized density operator on a finite multipartite Hilbert space $H=\bigotimes_{i=1}^{m+2}H_i$, where every local space has positive dimension. Separability means full multipartite separability. All logarithms are base two. Let $F(\alpha,\beta)=(\operatorname{Tr}\sqrt{\sqrt\alpha\,\beta\sqrt\alpha})^2$ be squared Uhlmann fidelity.
--
--   Here $E_{\max}(\alpha)=\inf_{\sigma\in\mathcal S}\inf\{\log_2 s:\alpha\le s\sigma\}$ and $E_{\max}^{\varepsilon}(\alpha)=\min\{E_{\max}(\beta):\beta\text{ is normalized},\ F(\beta,\alpha)\ge1-\varepsilon\}$.
--
--   Global robustness $R_G(\alpha)$ is the smallest $s\ge0$ making $(\alpha+s\omega)/(1+s)$ separable with arbitrary normalized noise $\omega$. Let $\delta>0$ and $\varepsilon\ge0$. Suppose $\Lambda$ is CPTP and satisfies $R_G(\Lambda(\sigma))\le\delta$ for every fully separable state $\sigma$. Input and output local dimensions may differ. Then
--
--   $$
--   E_{\max}^{\varepsilon}(\Lambda(\rho))
--   \le E_{\max}^{\varepsilon}(\rho)+\log_2(1+\delta).
--   $$
--
--   This bounds smooth max-entanglement growth by the allowed entanglement generation. It applies to all delta-SEPP maps, with no LOCC restriction.
-- source:
--   One-shot rates for entanglement manipulation under non-entangling maps, arXiv:0905.2673v2, PDF p. 5, Lemma 2, Eq.(34)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P09

noncomputable section

open Filter Set

open scoped Topology Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P09

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

/-- PDF p.5, Lemma 2, Eq.(34): smooth max monotonicity with the finite log correction
on the right. The channel may change every local dimension. -/
theorem smoothMax_deltaSEPP_monotone {m : ℕ} (H J : MultipartiteSystem m) (rho : MultipartiteOperator H)
    (hrho : IsDensityMatrix rho) (delta eps : ℝ) (hdelta : 0 < delta) (heps : 0 ≤ eps)
    (Phi : Superop (ProductBasis H) (ProductBasis J)) (hPhi : IsDeltaSEPP delta Phi) :
    fidelitySmoothMaxEntanglement (Phi rho) eps ≤ fidelitySmoothMaxEntanglement rho eps + (logTwo (1 + delta) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P09

end
