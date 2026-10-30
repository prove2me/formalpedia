-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_moment_sequential_continuity
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.moment_sequential_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:42:25.700459+00:00
-- url     : https://prove2.me/theorems/73214d01-a64c-4710-8040-e47487654b78
-- title:
--   Lemma 4.1: sequential continuity of scaled logarithmic moments
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   A scheme with rate $I$ satisfies the closed-set upper and open-set lower large-deviation bounds for every input; $I(\rho,\cdot)$ is good and vanishes exactly at the target of $\rho$.
--
--   For a continuous real function $f$ on $\mathcal S$, set
--   $$h_N(\rho,f)=-\frac1N\log\int_{\mathcal S}e^{-Nf(\sigma)}\,\mu_{N,\rho}(d\sigma),\qquad h(\rho,f)=\inf_{\sigma\in\mathcal S}\{I(\rho,\sigma)+f(\sigma)\}.$$
--   These values are finite because $\mathcal S$ is compact and the scheme has a good rate with its unique zero at the true state.
--
--   Suppose a full-estimation scheme has rate $I$ and $\rho_N\to\rho$. If $\rho$ is positive definite, then
--   $$h_N(\rho_N,f)\longrightarrow h(\rho,f),\qquad h_N(\rho,f)\longrightarrow h(\rho,f).$$
--   If $I$ is jointly lower semicontinuous, arbitrary, possibly singular $\rho$ satisfies
--   $$\liminf_N h_N(\rho_N,f)\ge h(\rho,f).$$
--   This supplies continuity along moving input states; joint regularity is required only for the boundary lower bound.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 11, Lemma 4.1 / (37),(38)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.11-14, Lemma 4.1, (37)-(38): both clauses retain rho_N→rho.
Only the lower-bound clause assumes joint lower semicontinuity. -/
theorem moment_sequential_continuity {d : ℕ} (hd : 0 < d)
    (E : Scheme d (DensityOutcome d)) (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (hI : SchemeLDP E FullTarget I) (f : DensityOutcome d → ℝ) (hf : Continuous f)
    (rho : DensityOutcome d) (rhoSeq : ℕ → DensityOutcome d) (hseq : Tendsto rhoSeq atTop (nhds rho)) :
    (rho.val.PosDef →
      Tendsto (fun k => logLaplaceMoment E k (rhoSeq k) f) atTop (nhds (limitMoment I rho f)) ∧
      Tendsto (fun k => logLaplaceMoment E k rho f) atTop (nhds (limitMoment I rho f))) ∧
    (JointLSC I → (limitMoment I rho f : EReal) ≤
      Filter.liminf (fun k => (logLaplaceMoment E k (rhoSeq k) f : EReal)) atTop) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
