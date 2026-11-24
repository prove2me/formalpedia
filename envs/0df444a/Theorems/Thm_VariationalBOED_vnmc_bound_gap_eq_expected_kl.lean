-- Prove2me | Theorems.Thm_VariationalBOED_vnmc_bound_gap_eq_expected_kl
-- name    : VariationalBOED.vnmc_bound_gap_eq_expected_kl
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T16:46:19.686099+00:00
-- url     : https://prove2.me/theorems/9bff9388-7e20-4cca-bf97-51af06ef6221
-- title:
--   Lemma 1 (3): the gap of the VNMC bound is an expected KL divergence
-- statement:
--   Let $p(\theta)p(y\mid\theta,d)$ be a model with $\mathrm{EIG}(d)$ finite, let $q_v$ be a valid VNMC proposal, and let $L\ge1$. For each $y$ put
--
--   $$P(\theta_{1:L}\mid y,d)=\frac1L\sum_{\ell=1}^Lp(\theta_\ell\mid y,d)\prod_{k\ne\ell}q_v(\theta_k\mid y,d).$$
--
--   Then $\mathcal U_{\mathrm{VNMC}}(d,L)$ is finite if and only if $\mathbb E_{p(y\mid d)}\big[\mathrm{KL}\big(\prod_{\ell=1}^Lq_v(\theta_\ell\mid y,d)\,\|\,P(\theta_{1:L}\mid y,d)\big)\big]<\infty$. In that case
--
--   $$\mathcal U_{\mathrm{VNMC}}(d,L)-\mathrm{EIG}(d)=\mathbb E_{p(y\mid d)}\Big[\mathrm{KL}\Big(\prod_{\ell=1}^Lq_v(\theta_\ell\mid y,d)\,\Big\|\,P(\theta_{1:L}\mid y,d)\Big)\Big].$$
--
--   The gap of the VNMC bound is thus an expected KL divergence between the proposal's product law on $\Theta^L$ and a mixture that places the true posterior in one coordinate.
--
--   **Formalization Note** The paper's identity is in extended reals. Here $\mathrm{EIG}(d)$ is assumed finite, and the case $\mathcal U_{\mathrm{VNMC}}(d,L)=+\infty$ is stated as the equivalence between finiteness of the two sides.
-- source:
--   Foster, Jankowiak, Bingham, Horsfall, Teh, Rainforth and Goodman, Variational Bayesian Optimal Experimental Design, arXiv:1903.05480v3 (NeurIPS 2019), Section 3, Lemma 1 (3), eq. (10), p. 4; proof in Appendix A.3, eqs. (40)-(44), pp. 14-15

import Mathlib
import Definitions.Def_VariationalBOED_Basic

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal

namespace VariationalBOED

theorem vnmc_bound_gap_eq_expected_kl {Th Y : Type*} [MeasurableSpace Th] [MeasurableSpace Y]
    (nuT : Measure Th) (nuY : Measure Y) [SigmaFinite nuT] [SigmaFinite nuY]
    (p : Th → ℝ) (lik : Th → Y → ℝ) (hM : IsModel nuT nuY p lik)
    (qv : Y → Th → ℝ) (hq : IsValidVNMCProposal nuT p lik qv)
    (hEIG : Integrable (eigIntegrand nuT p lik) (jointLaw nuT nuY p lik))
    (L : ℕ) (hL : 1 ≤ L) :
    (Integrable (vnmcIntegrand p lik qv L) (vnmcLaw nuT nuY p lik qv L) ↔
      (∫⁻ y, klDiv (vnmcProposalProd nuT qv L y) (vnmcMixture nuT p lik qv L y)
        ∂marginalLaw nuT nuY p lik) ≠ ⊤) ∧
    (Integrable (vnmcIntegrand p lik qv L) (vnmcLaw nuT nuY p lik qv L) →
      vnmcBound nuT nuY p lik qv L - eig nuT nuY p lik =
        (∫⁻ y, klDiv (vnmcProposalProd nuT qv L y) (vnmcMixture nuT p lik qv L y)
          ∂marginalLaw nuT nuY p lik).toReal) := by sorry

end VariationalBOED
