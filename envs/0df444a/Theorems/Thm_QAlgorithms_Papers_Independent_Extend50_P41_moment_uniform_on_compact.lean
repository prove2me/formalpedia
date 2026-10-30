-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_moment_uniform_on_compact
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.moment_uniform_on_compact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:44:52.811953+00:00
-- url     : https://prove2.me/theorems/1cf02a42-9a2b-45e9-87a2-07271f36aa1d
-- title:
--   Proposition 4.4: uniform convergence on compact full-rank subsets
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   A scheme with rate $I$ satisfies the closed-set upper and open-set lower large-deviation bounds for every input; $I(\rho,\cdot)$ is good and vanishes exactly at the target of $\rho$.
--
--   For a continuous real function $f$ on $\mathcal S$, set
--   $$h_N(\rho,f)=-\frac1N\log\int_{\mathcal S}e^{-Nf(\sigma)}\,\mu_{N,\rho}(d\sigma),\qquad h(\rho,f)=\inf_{\sigma\in\mathcal S}\{I(\rho,\sigma)+f(\sigma)\}.$$
--   These values are finite because $\mathcal S$ is compact and the scheme has a good rate with its unique zero at the true state.
--
--   Suppose the full scheme has rate $I$ and $K\subseteq\mathcal S$ is compact and consists of positive-definite states. Then $h_N(\cdot,f)$ converges uniformly to $h(\cdot,f)$ on $K$:
--   $$\forall\varepsilon>0\ \exists N_\varepsilon\ \forall N\ge N_\varepsilon\ \forall\rho\in K:\quad |h_N(\rho,f)-h(\rho,f)|<\varepsilon.$$
--   The formulation includes empty $K$ and provides a threshold independent of the chosen input in $K$.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 15, Proposition 4.4 / (63)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.14-15, Proposition 4.4, (63): epsilon formulation includes empty K.
The preceding prose pins the assumptions to Lemma 4.1, despite the printed
cross-reference to the preceding (purely topological) lemma. -/
theorem moment_uniform_on_compact {d : ℕ} (hd : 0 < d)
    (E : Scheme d (DensityOutcome d)) (I : DensityOutcome d → DensityOutcome d → ℝ≥0∞)
    (hI : SchemeLDP E FullTarget I) (f : DensityOutcome d → ℝ) (hf : Continuous f)
    (K : Set (DensityOutcome d)) (hK : IsCompact K) (hpos : ∀ rho ∈ K, rho.val.PosDef) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ threshold : ℕ, ∀ k, threshold ≤ k →
      ∀ rho ∈ K, |logLaplaceMoment E k rho f - limitMoment I rho f| < epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
