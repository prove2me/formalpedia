-- Prove2me | Theorems.Thm_VariationalBOED_marginal_bound_ge_eig
-- name    : VariationalBOED.marginal_bound_ge_eig
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T16:17:34.634672+00:00
-- url     : https://prove2.me/theorems/093440df-c12e-4e70-a524-5f6c3d93f348
-- title:
--   Appendix A.2 (eq. 9): the variational marginal bound is an upper bound on the EIG
-- statement:
--   Let $p(\theta)p(y\mid\theta,d)$ be a model and let $q_m(y\mid d)$ be a valid marginal approximation, that is, a probability density with the same support as $p(y\mid d)$. Suppose $\mathrm{EIG}(d)$ and $\mathcal U_{\mathrm{marg}}(d)$ are finite. Then $\mathrm{KL}(p(y\mid d)\,\|\,q_m(y\mid d))<\infty$,
--
--   $$\mathcal U_{\mathrm{marg}}(d)-\mathrm{EIG}(d)=\mathrm{KL}\big(p(y\mid d)\,\|\,q_m(y\mid d)\big)\ge0,$$
--
--   and $\mathcal U_{\mathrm{marg}}(d)=\mathrm{EIG}(d)$ if and only if $q_m(y\mid d)=p(y\mid d)$ for $\nu_{\mathcal Y}$-almost all $y$.
--
--   This upper bound underlies the variational marginal estimator $\hat\mu_{\mathrm{marg}}$, which is trained by minimizing $\mathcal U_{\mathrm{marg}}$.
--
--   **Formalization Note** Finiteness of $\mathrm{EIG}(d)$ and $\mathcal U_{\mathrm{marg}}(d)$ is assumed explicitly. The KL divergence is Mathlib's `klDiv`.
-- source:
--   Foster, Jankowiak, Bingham, Horsfall, Teh, Rainforth and Goodman, Variational Bayesian Optimal Experimental Design, arXiv:1903.05480v3 (NeurIPS 2019), Section 3, eq. (9), p. 4; proof in Appendix A.2, eqs. (23)-(27), p. 13

import Mathlib
import Definitions.Def_VariationalBOED_Basic

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal

namespace VariationalBOED

theorem marginal_bound_ge_eig {Th Y : Type*} [MeasurableSpace Th] [MeasurableSpace Y]
    (nuT : Measure Th) (nuY : Measure Y) [SigmaFinite nuT] [SigmaFinite nuY]
    (p : Th → ℝ) (lik : Th → Y → ℝ) (hM : IsModel nuT nuY p lik)
    (qm : Y → ℝ) (hqm : IsValidMarginalApprox nuT nuY p lik qm)
    (hEIG : Integrable (eigIntegrand nuT p lik) (jointLaw nuT nuY p lik))
    (hU : Integrable (margIntegrand lik qm) (jointLaw nuT nuY p lik)) :
    klDiv (densMeasure nuY (marginal nuT p lik)) (densMeasure nuY qm) ≠ ⊤ ∧
    margBound nuT nuY p lik qm - eig nuT nuY p lik =
      (klDiv (densMeasure nuY (marginal nuT p lik)) (densMeasure nuY qm)).toReal ∧
    eig nuT nuY p lik ≤ margBound nuT nuY p lik qm ∧
    (margBound nuT nuY p lik qm = eig nuT nuY p lik ↔ qm =ᵐ[nuY] marginal nuT p lik) := by sorry

end VariationalBOED
