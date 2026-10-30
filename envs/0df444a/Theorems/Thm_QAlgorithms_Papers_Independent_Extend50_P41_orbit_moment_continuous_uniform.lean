-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_orbit_moment_continuous_uniform
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.orbit_moment_continuous_uniform
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:47:06.148779+00:00
-- url     : https://prove2.me/theorems/e5fd5c93-4afc-4389-bce7-5d5806887c84
-- title:
--   Proposition 4.7: continuous limiting orbit moment and uniform convergence
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   A scheme with rate $I$ satisfies the closed-set upper and open-set lower large-deviation bounds for every input; $I(\rho,\cdot)$ is good and vanishes exactly at the target of $\rho$.
--
--   For a continuous real function $f$ on $\mathcal S$, set
--   $$h_N(\rho,f)=-\frac1N\log\int_{\mathcal S}e^{-Nf(\sigma)}\,\mu_{N,\rho}(d\sigma),\qquad h(\rho,f)=\inf_{\sigma\in\mathcal S}\{I(\rho,\sigma)+f(\sigma)\}.$$
--   These values are finite because $\mathcal S$ is compact and the scheme has a good rate with its unique zero at the true state.
--
--   For $U\in U(d)$ put $\alpha_U f(\sigma)=f(U\sigma U^*)$.
--
--   Fix positive-definite $\rho$. Then the function
--   $$g(U)=h(U^*\rho U,\alpha_Uf)=\inf_{\sigma\in\mathcal S}\{I(U^*\rho U,U^*\sigma U)+f(\sigma)\}$$
--   is continuous on $U(d)$, and
--   $$\forall\varepsilon>0\ \exists N_\varepsilon\ \forall N\ge N_\varepsilon\ \forall U\in U(d):\quad |h_N(U^*\rho U,\alpha_Uf)-g(U)|<\varepsilon.$$
--   This gives one convergence threshold for the whole unitary orbit.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 16, Proposition 4.7 / (77),(78)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.16-17, Proposition 4.7, (77)-(78): continuity, the orbit-infimum
identity and uniform convergence over all U(d). -/
theorem orbit_moment_continuous_uniform {d : ℕ} (hd : 0 < d)
    (E : Scheme d (DensityOutcome d)) (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (hI : SchemeLDP E FullTarget I) (f : DensityOutcome d → ℝ) (hf : Continuous f)
    (rho : DensityOutcome d) (hpos : rho.val.PosDef) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      limitMoment I (conjugateState U⁻¹ rho) (actionTest U f)) ∧
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      (limitMoment I (conjugateState U⁻¹ rho) (actionTest U f) : EReal) =
        ⨅ sigma, (I (conjugateState U⁻¹ rho) (conjugateState U⁻¹ sigma) : EReal) + (f sigma : EReal)) ∧
    ∀ epsilon : ℝ, 0 < epsilon → ∃ threshold : ℕ, ∀ k, threshold ≤ k →
      ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        |logLaplaceMoment E k (conjugateState U⁻¹ rho) (actionTest U f) -
          limitMoment I (conjugateState U⁻¹ rho) (actionTest U f)| < epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
