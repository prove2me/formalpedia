-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_limiting_moment_continuousAt
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.limiting_moment_continuousAt
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:45:30.940237+00:00
-- url     : https://prove2.me/theorems/716eca7c-6387-45ec-8352-4f17e4a672b7
-- title:
--   Proposition 4.5: continuity of limiting logarithmic moment on the interior
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   A scheme with rate $I$ satisfies the closed-set upper and open-set lower large-deviation bounds for every input; $I(\rho,\cdot)$ is good and vanishes exactly at the target of $\rho$.
--
--   For a continuous real function $f$ on $\mathcal S$, set
--   $$h_N(\rho,f)=-\frac1N\log\int_{\mathcal S}e^{-Nf(\sigma)}\,\mu_{N,\rho}(d\sigma),\qquad h(\rho,f)=\inf_{\sigma\in\mathcal S}\{I(\rho,\sigma)+f(\sigma)\}.$$
--   These values are finite because $\mathcal S$ is compact and the scheme has a good rate with its unique zero at the true state.
--
--   For a full scheme with rate $I$, at every positive-definite $\rho$ the real-valued function on the whole state space is continuous:
--   $$\tau\longmapsto h(\tau,f)\quad\text{is continuous at }\rho.$$
--   No additional regularity of $I$ is assumed. The conclusion concerns the limiting logarithmic moment, rather than continuity of the rate itself.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 15, Proposition 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.15, Proposition 4.5: continuity on the whole state space at each
positive-definite input, without a joint continuity premise on I. -/
theorem limiting_moment_continuousAt {d : ℕ} (hd : 0 < d)
    (E : Scheme d (DensityOutcome d)) (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (hI : SchemeLDP E FullTarget I) (f : DensityOutcome d → ℝ) (hf : Continuous f)
    (rho : DensityOutcome d) (hpos : rho.val.PosDef) :
    ContinuousAt (fun tau => limitMoment I tau f) rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
