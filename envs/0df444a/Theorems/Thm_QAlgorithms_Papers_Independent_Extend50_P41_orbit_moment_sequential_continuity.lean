-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_orbit_moment_sequential_continuity
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.orbit_moment_sequential_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:46:28.569975+00:00
-- url     : https://prove2.me/theorems/d02efcc4-d30a-4330-a800-9deac4a7f14a
-- title:
--   Lemma 4.6: continuity under convergent unitary conjugations
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
--   Let $U_N\to U$ in $U(d)$. If $\rho$ is positive definite, then
--   $$h_N(U_N^*\rho U_N,\alpha_{U_N}f)\longrightarrow h(U^*\rho U,\alpha_Uf),\qquad h_N(U^*\rho U,\alpha_Uf)\longrightarrow h(U^*\rho U,\alpha_Uf).$$
--   If $I$ is jointly lower semicontinuous, arbitrary $\rho$ satisfies
--   $$\liminf_N h_N(U_N^*\rho U_N,\alpha_{U_N}f)\ge h(U^*\rho U,\alpha_Uf).$$
--   The moving density and moving test function both matter to this orbit-continuity result.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 15, Lemma 4.6 / (66),(67)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.15-16, Lemma 4.6, (66)-(67): inverse conjugation of the density
argument and forward conjugation of the test function, with the fixed-U clause. -/
theorem orbit_moment_sequential_continuity {d : ℕ} (hd : 0 < d)
    (E : Scheme d (DensityOutcome d)) (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (hI : SchemeLDP E FullTarget I) (f : DensityOutcome d → ℝ) (hf : Continuous f)
    (rho : DensityOutcome d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (uSeq : ℕ → Matrix.unitaryGroup (Fin d) ℂ) (hu : Tendsto uSeq atTop (nhds U)) :
    (rho.val.PosDef →
      Tendsto (fun k => logLaplaceMoment E k (conjugateState (uSeq k)⁻¹ rho) (actionTest (uSeq k) f))
        atTop (nhds (limitMoment I (conjugateState U⁻¹ rho) (actionTest U f))) ∧
      Tendsto (fun k => logLaplaceMoment E k (conjugateState U⁻¹ rho) (actionTest U f))
        atTop (nhds (limitMoment I (conjugateState U⁻¹ rho) (actionTest U f)))) ∧
    (JointLSC I → (limitMoment I (conjugateState U⁻¹ rho) (actionTest U f) : EReal) ≤
      Filter.liminf (fun k =>
        (logLaplaceMoment E k (conjugateState (uSeq k)⁻¹ rho) (actionTest (uSeq k) f) : EReal)) atTop) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
