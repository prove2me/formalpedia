-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P08_entropyContinuityBound
-- name    : QAlgorithms.Papers.Independent.Frontier18.P08.entropyContinuityBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:57:38.001987+00:00
-- url     : https://prove2.me/theorems/5f9fd39e-48d5-4f99-8e16-b1bd4427bc79
-- title:
--   Unnumbered (15): finite-dimensional entropy continuity
-- statement:
--   Let $\rho$ and $\sigma$ be normalized density operators on a complex Hilbert space of finite positive dimension $d$. Write $H(\rho)=-\operatorname{Tr}(\rho\log\rho)$ and $h_2(t)=-t\log t-(1-t)\log(1-t)$, using natural logarithms and $0\log0=0$. If $\varepsilon=\tfrac12\|\rho-\sigma\|_1<1$, then
--
--   $$
--   |H(\rho)-H(\sigma)|\le\varepsilon\log d+(1+\varepsilon)h_2\!\left(\frac{\varepsilon}{1+\varepsilon}\right).
--   $$
--
--   This is the paper's explicit entropy modulus (15), including $\varepsilon=0$. It is not replaced by the subsequently cited sharper Audenaert bound.
-- source:
--   Measures of quantum correlations in infinite-dimensional systems, arXiv:1506.06377v2, PDF p. 11, Unnumbered (15): finite-dimensional entropy continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08

noncomputable section

open Filter

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P08

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

/-- Bound (15), PDF p.11, with the trace-distance convention in Proposition 1,
PDF p.10: normalized states, natural logs, and epsilon = half trace norm < 1.
The endpoint epsilon = 0 is included. -/
theorem entropyContinuityBound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hRho : IsDensityMatrix rho)
    (hSigma : IsDensityMatrix sigma) (epsilon : ℝ)
    (hDistance : epsilon = traceNorm (rho - sigma) / 2)
    (hEpsilon : epsilon < 1) :
    |Real.log 2 * vnEntropy rho - Real.log 2 * vnEntropy sigma| ≤
      epsilon * Real.log (Fintype.card I : ℝ) +
        (1 + epsilon) * Real.binEntropy (epsilon / (1 + epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P08

end
