-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_varianceEstimatorAsymptotics
-- name    : QAlgorithms.Papers.Independent.Information100.P37.varianceEstimatorAsymptotics
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:14:44.766136+00:00
-- url     : https://prove2.me/theorems/334a1b3e-5a03-4717-956a-30372589cc7a
-- title:
--   §VI.C, Eqs. (65)–(66): variance/deviation estimators
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   For iid populations with law $\nu_d$, define $\widetilde C_N=N^{-1}\sum_jX_U(p_j)$ and, for $N\ge2$, $\widetilde V_N=(N-1)^{-1}\sum_j(X_U(p_j)-\widetilde C_N)^2$. Let $\mu_4=\mathbb E(X_U-C_U)^4$ and $v=\mu_4-\Delta_U^4\ge0$. Then
--   $$\mathbb E\widetilde V_N=\Delta_U^2,\qquad \sqrt N(\widetilde V_N-\Delta_U^2)\Rightarrow\mathcal N(0,v).$$
--   If $\Delta_U>0$, then
--   $$\sqrt N(\sqrt{\widetilde V_N}-\Delta_U)\Rightarrow\mathcal N\left(0,\frac{v}{4\Delta_U^2}\right).$$
--   Convergence is weak convergence of the induced laws; a Gaussian with variance zero is a point mass. Arbitrary total-function values at $N=0,1$ do not affect either limit.
--
--   The fourth central moment controls the asymptotic accuracy of variance and deviation estimation.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 8, §VI.C, Eqs. (65)–(66): variance/deviation estimators

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.8, (65)--(66): unbiased variance, weak CLT and square-root delta method. -/
theorem varianceEstimatorAsymptotics [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    let E := conjSuperop U
    let v := fourthCentral E - cgpd E ^ 4
    (∀ N : ℕ, 2 ≤ N → (∫ p, sampleVariance E p ∂sampleLaw ι N) = cgpd E ^ 2) ∧
    0 ≤ v ∧
    LawsConverge (fun N => Measure.map (fun p : Fin N → (ι → ℝ) =>
      Real.sqrt (N : ℝ) * (sampleVariance E p - cgpd E ^ 2)) (sampleLaw ι N))
      (gaussianReal 0 (Real.toNNReal v)) ∧
    (0 < cgpd E → LawsConverge (fun N => Measure.map (fun p : Fin N → (ι → ℝ) =>
      Real.sqrt (N : ℝ) * (Real.sqrt (sampleVariance E p) - cgpd E)) (sampleLaw ι N))
      (gaussianReal 0 (Real.toNNReal (v / (4 * cgpd E ^ 2))))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
