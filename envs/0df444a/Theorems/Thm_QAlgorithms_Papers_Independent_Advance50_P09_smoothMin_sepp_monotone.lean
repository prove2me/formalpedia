-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P09_smoothMin_sepp_monotone
-- name    : QAlgorithms.Papers.Independent.Advance50.P09.smoothMin_sepp_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:33:32.384728+00:00
-- url     : https://prove2.me/theorems/e1e9b38e-a14f-4831-a27e-c90b6a78d6dd
-- title:
--   Operator-smoothed min entanglement is SEPP monotone
-- statement:
--   Let $\rho$ be a normalized density operator on a finite multipartite Hilbert space $H=\bigotimes_{i=1}^{m+2}H_i$, where every local space has positive dimension. Separability means full multipartite separability. All logarithms are base two. Let $F(\alpha,\beta)=(\operatorname{Tr}\sqrt{\sqrt\alpha\,\beta\sqrt\alpha})^2$ be squared Uhlmann fidelity.
--
--   Here $E_{\min}^{\varepsilon}(\rho)=\max_{0\le A\le I,\,\operatorname{Tr}(A\rho)\ge1-\varepsilon}\min_{\sigma\in\mathcal S(H)}[-\log_2\operatorname{Tr}(A\sigma)]$ is the operator-smoothed min-relative entropy of entanglement, with $-\log_2 0=+\infty$.
--
--   Let $\Lambda$ be a CPTP separability-preserving map to another finite system with the same parties, allowing different local dimensions. For every $\varepsilon\ge0$,
--
--   $$
--   E_{\min}^{\varepsilon}(\Lambda(\rho))\le E_{\min}^{\varepsilon}(\rho).
--   $$
--
--   This is monotonicity of the source's test-operator smoothing under non-entangling operations. It includes $\varepsilon=0$; at $\varepsilon\ge1$ both sides are positive infinity because the zero effect is feasible.
-- source:
--   One-shot rates for entanglement manipulation under non-entangling maps, arXiv:0905.2673v2, PDF p. 4, Lemma 1, Eq.(25)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P09

noncomputable section

open Filter Set

open scoped Topology Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P09

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

/-- PDF p.4, Lemma 1, Eq.(25): operator-smoothed min monotonicity, including eps = 0
and the infinite zero-effect branch eps >= 1. -/
theorem smoothMin_sepp_monotone {m : ℕ} (H J : MultipartiteSystem m) (rho : MultipartiteOperator H)
    (hrho : IsDensityMatrix rho) (eps : ℝ) (heps : 0 ≤ eps)
    (Phi : Superop (ProductBasis H) (ProductBasis J)) (hPhi : IsSEPP Phi) :
    operatorSmoothMinEntanglement (Phi rho) eps ≤ operatorSmoothMinEntanglement rho eps := by sorry

end QAlgorithms.Papers.Independent.Advance50.P09

end
