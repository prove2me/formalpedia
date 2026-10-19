-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P08_conditionalEntropyContinuityBound
-- name    : QAlgorithms.Papers.Independent.Frontier18.P08.conditionalEntropyContinuityBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:58:14.364988+00:00
-- url     : https://prove2.me/theorems/7748a49b-baec-4e44-95d3-907f415d76da
-- title:
--   Unnumbered (16): finite-dimensional conditional entropy continuity
-- statement:
--   Let $A$ and $B$ be finite-dimensional complex quantum systems with positive dimensions, and let $\rho_{AB},\sigma_{AB}$ be normalized density operators. Define the original conditional entropy by $H(A|B)_\rho=H(\rho_{AB})-H(\rho_B)$, where $\rho_B=\operatorname{Tr}_A\rho_{AB}$ and $H$ uses natural logarithms. If $d_A=\dim H_A$ and $\varepsilon=\tfrac12\|\rho_{AB}-\sigma_{AB}\|_1<1$, then
--
--   $$
--   |H(A|B)_\rho-H(A|B)_\sigma|
--   \le2\varepsilon\log d_A+(1+\varepsilon)h_2\!\left(\frac{\varepsilon}{1+\varepsilon}\right),
--   $$
--
--   where $h_2$ is binary entropy with natural logarithms and $0\log0=0$.
--
--   This is the original finite-dimensional bound (16), including $\varepsilon=0$. Corollary 5, which extends it to arbitrary $B$, remains a separately deferred node.
-- source:
--   Measures of quantum correlations in infinite-dimensional systems, arXiv:1506.06377v2, PDF p. 12, Unnumbered (16): finite-dimensional conditional entropy continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08

noncomputable section

open Filter

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P08

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

/-- Bound (16), PDF p.12 (continued from p.11): the ORIGINAL conditional
entropy for finite-dimensional A and B. Corollary 5 is the separate result
for arbitrary B; it is explicitly deferred, not restricted to finite B. -/
theorem conditionalEntropyContinuityBound {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J]
    (rho sigma : Matrix (I × J) (I × J) ℂ)
    (hRho : IsDensityMatrix rho) (hSigma : IsDensityMatrix sigma) (epsilon : ℝ)
    (hDistance : epsilon = traceNorm (rho - sigma) / 2)
    (hEpsilon : epsilon < 1) :
    |conditionalEntropyNats rho - conditionalEntropyNats sigma| ≤
      2 * epsilon * Real.log (Fintype.card I : ℝ) +
        (1 + epsilon) * Real.binEntropy (epsilon / (1 + epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P08

end
