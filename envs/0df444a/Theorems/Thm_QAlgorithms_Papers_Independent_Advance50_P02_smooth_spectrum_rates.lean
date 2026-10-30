-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_smooth_spectrum_rates
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.smooth_spectrum_rates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:34:52.719701+00:00
-- url     : https://prove2.me/theorems/2aa98dfe-64ca-46d8-9f88-994e613746d3
-- title:
--   Arbitrary-error smooth-max/spectrum identities
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. For an arbitrary sequence of finite-dimensional normalized pairs $(\rho_n,\sigma_n)$, index only positive blocklengths. All rate optimizations and limit extrema are extended real. Write $G_n(R)=\operatorname{tr}\rho_n\{\rho_n\le2^{nR}\sigma_n\}$, $\underline D^\varepsilon=\sup\{R:\limsup G_n(R)\le\varepsilon\}$, and $\overline D^\varepsilon=\sup\{R:\liminf G_n(R)<\varepsilon\}$. Assume either the number of distinct eigenvalues of $\sigma_n$ is eventually bounded by $C n^d$, or the negative logarithm of its smallest eigenvalue is so bounded. Constants $C>0$, $d$ and the threshold precede $n$. In the second alternative, a supported restriction is allowed only with explicit $\operatorname{supp}\rho_n\subseteq\operatorname{supp}\sigma_n$. For $0<\varepsilon<1$,
--   $$\underline D^\varepsilon=\sup_{\limsup\varepsilon_n\le\varepsilon}\liminf_n\frac1nD_{\max}^{\sqrt{1-\varepsilon_n}}(\rho_n\Vert\sigma_n),$$
--   $$\overline D^\varepsilon=\sup_{\liminf\varepsilon_n<\varepsilon}\liminf_n\frac1nD_{\max}^{\sqrt{1-\varepsilon_n}}(\rho_n\Vert\sigma_n).$$
--   All error sequences lie in $[0,1]$. At smoothing parameter one, use the monotone left limit $\inf_{0\le b<1}D_{\max}^b$, explicitly preserving infinities. This extends the spectrum correspondence to arbitrary interior target errors.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 23, §VIII: arbitrary-error smooth-max/spectrum identities

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Section VIII, PDF p.23: sqrt(1-epsilon_n) is retained, with arbitrary
probability-valued error sequences and an explicit endpoint limit convention. Source correction. Printed: Definition 2 requires smoothing radius below 1, whereas p.23 permits sqrt(1-epsilon_n)=1; its spectral condition refers to the minimum eigenvalue.
Changed: At smoothing 1 use the explicit monotone left limit inf_{0<=b<1} Dmax^b; the second spectral alternative uses positive support with explicit support inclusion.
Why: At an interior target error, zero sequence entries can be approximated from above by positive entries without changing the optimized rate. The continuation is explicit and preserves infinities. Support restriction removes only unused kernel directions; the distinct-eigenvalue alternative is retained. -/
theorem smooth_spectrum_rates (S : PairSequence) (hS : StateSequence S)
    (hcontrol : SpectralControl S) (e : ℝ) (he : 0 < e ∧ e < 1) :
    quantumSpectrumRate S e false =
      optimizedEntropySequenceRate (fun k a => smoothMaxEndpoint (Real.sqrt (1-a)) (S.rho k) (S.sigma k)) e false ∧
    quantumSpectrumRate S e true =
      optimizedEntropySequenceRate (fun k a => smoothMaxEndpoint (Real.sqrt (1-a)) (S.rho k) (S.sigma k)) e true := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
