-- Prove2me | Theorems.Thm_VariationalBOED_eig_ge_posterior_bound
-- name    : VariationalBOED.eig_ge_posterior_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T16:04:35.079026+00:00
-- url     : https://prove2.me/theorems/095677ec-19eb-486e-b631-ac0c2c68ee3e
-- title:
--   Appendix A.1 (eq. 6): the variational posterior bound is a lower bound on the EIG
-- statement:
--   Let $p(\theta)p(y\mid\theta,d)$ be a model and let $q_p(\theta\mid y,d)$ be a valid posterior approximation, that is, a conditional density with the same support as the posterior $p(\theta\mid y,d)$. Suppose $\mathrm{EIG}(d)$ and $\mathcal L_{\mathrm{post}}(d)$ are finite. Then $\mathbb E_{p(y\mid d)}\big[\mathrm{KL}(p(\theta\mid y,d)\,\|\,q_p(\theta\mid y,d))\big]<\infty$,
--
--   $$\mathrm{EIG}(d)-\mathcal L_{\mathrm{post}}(d)=\mathbb E_{p(y\mid d)}\big[\mathrm{KL}\big(p(\theta\mid y,d)\,\|\,q_p(\theta\mid y,d)\big)\big]\ge0,$$
--
--   and the bound is tight, $\mathcal L_{\mathrm{post}}(d)=\mathrm{EIG}(d)$, if and only if $q_p(\theta\mid y,d)=p(\theta\mid y,d)$ for $\nu_\Theta$-almost all $\theta$, for $p(y\mid d)$-almost all $y$.
--
--   This is the Barber–Agakov bound used to train the variational posterior estimator $\hat\mu_{\mathrm{post}}$: maximizing $\mathcal L_{\mathrm{post}}$ minimizes the expected forward KL divergence.
--
--   **Formalization Note** The paper states the bound for real-valued expectations, so finiteness of $\mathrm{EIG}(d)$ and $\mathcal L_{\mathrm{post}}(d)$ is assumed explicitly. The KL divergence is Mathlib's `klDiv` of the measures with densities $p(\cdot\mid y,d)$ and $q_p(\cdot\mid y,d)$, with values in $[0,\infty]$.
-- source:
--   Foster, Jankowiak, Bingham, Horsfall, Teh, Rainforth and Goodman, Variational Bayesian Optimal Experimental Design, arXiv:1903.05480v3 (NeurIPS 2019), Section 3, eq. (6) and the paragraph after it, p. 3; proof in Appendix A.1, eqs. (16)-(22), p. 13

import Mathlib
import Definitions.Def_VariationalBOED_Basic

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal

namespace VariationalBOED

theorem eig_ge_posterior_bound {Th Y : Type*} [MeasurableSpace Th] [MeasurableSpace Y]
    (nuT : Measure Th) (nuY : Measure Y) [SigmaFinite nuT] [SigmaFinite nuY]
    (p : Th → ℝ) (lik : Th → Y → ℝ) (hM : IsModel nuT nuY p lik)
    (q : Y → Th → ℝ) (hq : IsValidPosteriorApprox nuT p lik q)
    (hEIG : Integrable (eigIntegrand nuT p lik) (jointLaw nuT nuY p lik))
    (hL : Integrable (postIntegrand p q) (jointLaw nuT nuY p lik)) :
    (∫⁻ y, klDiv (densMeasure nuT (posterior nuT p lik y)) (densMeasure nuT (q y))
        ∂marginalLaw nuT nuY p lik) ≠ ⊤ ∧
    eig nuT nuY p lik - postBound nuT nuY p lik q =
      (∫⁻ y, klDiv (densMeasure nuT (posterior nuT p lik y)) (densMeasure nuT (q y))
        ∂marginalLaw nuT nuY p lik).toReal ∧
    postBound nuT nuY p lik q ≤ eig nuT nuY p lik ∧
    (postBound nuT nuY p lik q = eig nuT nuY p lik ↔
      ∀ᵐ y ∂marginalLaw nuT nuY p lik, q y =ᵐ[nuT] posterior nuT p lik y) := by sorry

end VariationalBOED
